#!/usr/bin/env python3
# Copyright 2026 Craig Tiller
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
scripts/task_frontier.py - Leverage-ranked task frontier for gasm

Parses docs/tasks/*.md frontmatter (a flat YAML subset — no external `yaml` dependency;
see `parse_frontmatter` for the tolerant hand-rolled grammar this tool accepts) and answers
one question: of the tasks that are actionable *right now*, which ones matter most?

"Matters most" is PageRank ("leverage" below) run over the task DAG, personalized by each
task's intrinsic `priority`, with rank flowing from dependents to prerequisites: a task
`B` with `after: [A]` contributes an edge B -> A (B depends on A, so wanting B done pushes
importance onto A — the thing that must land first). `related:` linksets contribute
symmetric edges at a lower weight, so genuinely-associated-but-not-blocking tasks still
share some leverage without distorting the dependency signal. Priority itself is *not*
static: it ages upward over time (see AGING_RATE below) so a merely-important task cannot
be permanently outranked by a once-more-urgent one that never gets picked up — see
`effective_priority`.

Validation (HARD-FAILS, exit 1): unparseable frontmatter, duplicate `id`s across files,
`after`/`related` entries referencing unknown ids, an invalid `status`, and a missing or
non-float `priority`. This overlaps what TC13 (docs/tasks/TC13-task-dag-tooling.md, the
planned task-DAG checker that also regenerates TASKS.md's status board) is expected to do;
TC13 may absorb or supersede this validation path entirely — this tool's parser and
validation were written to be lifted wholesale if so, rather than reinvented.

Usage:
    python scripts/task_frontier.py                 # frontier view (default)
    python scripts/task_frontier.py --all            # full ranking, every task
    python scripts/task_frontier.py --track proof-arch
    python scripts/task_frontier.py --json
    python scripts/task_frontier.py --validate        # checks only, no ranking output
"""

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Docs contain Unicode (arrows, math quantifiers, em-dashes); never let a legacy console
# codepage turn a report line into a crash. (Mirrors scripts/check_refs.py.)
if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent
TASKS_DIR = REPO_ROOT / "docs" / "tasks"

# --- Tunable constants (owner-specified; keep these the single source of truth) ---
DEP_WEIGHT = 1.0        # weight of a B->A edge from B's `after: [A]`
RELATED_WEIGHT = 0.3    # weight of each symmetric edge from a `related:` linkset
DAMPING = 0.85          # PageRank damping factor
MAX_ITER = 300
CONVERGENCE_TOL = 1e-12
AGING_RATE = 1.0        # effective_priority points added per hour since priority_set

VALID_STATUSES = {"blocked", "ready", "designing", "design-review", "implementing", "done"}
ACTIONABLE_STATUSES = {"ready", "designing", "design-review", "implementing"}

REQUIRED_FIELDS = [
    "id", "title", "status", "blocked_on", "after", "related", "bar", "track",
    "priority", "priority_set", "design", "design_review", "date",
]

FRONTMATTER_RE = re.compile(r"^---\r?\n(.*?)\r?\n---\r?\n", re.DOTALL)
KEY_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$")


class FrontmatterError(Exception):
    """Raised for anything that makes a task file's frontmatter unparseable or invalid."""


def parse_scalar_or_list(key: str, raw: str, file_label: str, line_no: int):
    raw = raw.strip()
    if raw == "":
        return ""
    if raw.startswith('"'):
        if not raw.endswith('"') or len(raw) < 2:
            raise FrontmatterError(f"{file_label}:{line_no}: unterminated quoted value for '{key}'")
        return raw[1:-1]
    if raw.startswith("["):
        if not raw.endswith("]"):
            raise FrontmatterError(f"{file_label}:{line_no}: unterminated list for '{key}'")
        inner = raw[1:-1].strip()
        if inner == "":
            return []
        items = [tok.strip() for tok in inner.split(",")]
        for tok in items:
            if tok == "" or " " in tok:
                raise FrontmatterError(
                    f"{file_label}:{line_no}: malformed list entry {tok!r} for '{key}'"
                )
        return items
    return raw


def parse_frontmatter(text: str, file_label: str) -> Dict:
    """
    Tolerant flat-YAML-subset parser for this project's task frontmatter. Supports only:
    bare scalars, "quoted strings" (including ""), and [comma, separated, lists] of bare
    tokens. No nesting, no multi-line values, no YAML anchors/tags/comments. Anything else
    is a hard parse failure — this is deliberately strict about the one shape this repo
    actually uses, not a general YAML parser.
    """
    m = FRONTMATTER_RE.match(text)
    if not m:
        raise FrontmatterError(f"{file_label}: no '---'-delimited frontmatter block found at top of file")
    body = m.group(1)
    fields: Dict = {}
    for i, raw_line in enumerate(body.split("\n"), start=1):
        line = raw_line.rstrip("\r")
        if line.strip() == "":
            continue
        km = KEY_RE.match(line)
        if not km:
            raise FrontmatterError(f"{file_label}:{i}: unparseable frontmatter line: {line!r}")
        key, raw_value = km.group(1), km.group(2)
        if key in fields:
            raise FrontmatterError(f"{file_label}:{i}: duplicate key '{key}' in frontmatter")
        fields[key] = parse_scalar_or_list(key, raw_value, file_label, i)
    for required in REQUIRED_FIELDS:
        if required not in fields:
            raise FrontmatterError(f"{file_label}: missing required frontmatter field '{required}'")
    return fields


class Task:
    __slots__ = (
        "id", "title", "status", "blocked_on", "after", "related", "bar", "track",
        "priority", "priority_set", "design", "design_review", "date", "file",
    )

    def __init__(self, fields: Dict, file: Path):
        self.id = fields["id"]
        self.title = fields["title"]
        self.status = fields["status"]
        self.blocked_on = fields["blocked_on"]
        self.after = list(fields["after"]) if isinstance(fields["after"], list) else []
        self.related = list(fields["related"]) if isinstance(fields["related"], list) else []
        self.bar = fields["bar"]
        self.track = fields["track"]
        self.priority = fields["priority"]
        self.priority_set = fields["priority_set"]
        self.design = fields["design"]
        self.design_review = fields["design_review"]
        self.date = fields["date"]
        self.file = file


def load_tasks() -> Tuple[List[Task], List[str]]:
    """Returns (tasks, errors). Parsing errors are collected, not raised immediately, so a
    single broken file reports alongside every other problem in one pass."""
    errors: List[str] = []
    tasks: List[Task] = []
    if not TASKS_DIR.is_dir():
        raise SystemExit(f"[!] docs/tasks/ not found at {TASKS_DIR}")
    for path in sorted(TASKS_DIR.glob("*.md")):
        rel = path.relative_to(REPO_ROOT).as_posix()
        try:
            text = path.read_text(encoding="utf-8")
        except Exception as e:
            errors.append(f"{rel}: could not read file: {e}")
            continue
        try:
            fields = parse_frontmatter(text, rel)
        except FrontmatterError as e:
            errors.append(str(e))
            continue
        try:
            task = Task(fields, path)
        except Exception as e:
            errors.append(f"{rel}: {e}")
            continue
        tasks.append(task)
    return tasks, errors


def validate(tasks: List[Task], parse_errors: List[str]) -> List[str]:
    errors = list(parse_errors)
    seen_ids: Dict[str, Path] = {}
    for t in tasks:
        rel = t.file.relative_to(REPO_ROOT).as_posix()
        if t.id in seen_ids:
            other = seen_ids[t.id].relative_to(REPO_ROOT).as_posix()
            errors.append(f"duplicate id '{t.id}': {other} and {rel}")
        else:
            seen_ids[t.id] = t.file

        if t.status not in VALID_STATUSES:
            errors.append(f"{rel}: invalid status {t.status!r} (must be one of {sorted(VALID_STATUSES)})")

        if not isinstance(t.priority, str) or t.priority == "":
            errors.append(f"{rel}: missing priority")
        else:
            try:
                float(t.priority)
            except ValueError:
                errors.append(f"{rel}: priority {t.priority!r} is not a float")

        if not isinstance(t.priority_set, str) or t.priority_set == "":
            errors.append(f"{rel}: missing priority_set")
        else:
            try:
                _parse_iso8601(t.priority_set)
            except ValueError as e:
                errors.append(f"{rel}: priority_set {t.priority_set!r} is not a valid ISO-8601 datetime ({e})")

    known_ids = set(seen_ids.keys())
    for t in tasks:
        rel = t.file.relative_to(REPO_ROOT).as_posix()
        for a in t.after:
            if a not in known_ids:
                errors.append(f"{rel}: 'after' references unknown id '{a}'")
        for r in t.related:
            if r not in known_ids:
                errors.append(f"{rel}: 'related' references unknown id '{r}'")
    return errors


def _parse_iso8601(s: str) -> datetime:
    s2 = s.strip()
    if s2.endswith("Z"):
        s2 = s2[:-1] + "+00:00"
    dt = datetime.fromisoformat(s2)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt


def effective_priority(t: Task, now: Optional[datetime] = None) -> float:
    """priority + AGING_RATE * hours_since(priority_set). Computed at read time from the
    stamped timestamp — files are never rewritten just because time passed. At
    AGING_RATE=1.0/hr on a 0-10 base scale, age dominates the base priority within about a
    day, so among tasks with similar readiness the frontier trends toward oldest-since-set
    first. That is the stated intent (prohibit aging out, not a side effect to correct for):
    a task's priority_set is meant to be bumped only when it is deliberately re-triaged,
    which is the mechanism for re-ranking it back down."""
    if now is None:
        now = datetime.now(timezone.utc)
    base = float(t.priority)
    try:
        set_at = _parse_iso8601(t.priority_set)
    except ValueError:
        return base
    hours = max(0.0, (now - set_at).total_seconds() / 3600.0)
    return base + AGING_RATE * hours


def build_graph(tasks: List[Task]) -> Dict[str, List[Tuple[str, float]]]:
    by_id = {t.id: t for t in tasks}
    out_edges: Dict[str, List[Tuple[str, float]]] = {t.id: [] for t in tasks}
    for t in tasks:
        for a in t.after:
            if a in by_id:
                out_edges[t.id].append((a, DEP_WEIGHT))
        for r in t.related:
            if r in by_id:
                out_edges[t.id].append((r, RELATED_WEIGHT))
                out_edges[r].append((t.id, RELATED_WEIGHT))

    # Dangling-node convention: a task with no `after` and no `related` is a *root* of the
    # happens-after DAG (nothing left to point to) — often its most foundational,
    # most-depended-upon node (a landed gate everything else builds on), the opposite of a
    # web-graph dead end. Two tempting fixes were tried and rejected empirically (both
    # produced rankings that failed this tool's own sanity check against common sense):
    # (1) teleporting a dangling node's mass out to the whole graph via the personalization
    # vector inflated unrelated, dependent-free, merely-high-priority nodes far above
    # genuinely load-bearing hub tasks; (2) self-looping a dangling node so it keeps 100% of
    # its accumulated rank forever over-amplified roots relative to any node that forwards
    # rank onward (which keeps only a `(1-DAMPING)` sliver of its own personalization) by a
    # factor of `1/(1-DAMPING)` — this let an isolated, dependent-free task outrank a task
    # with several real dependents. The convention below does neither: a dangling node's
    # in-flow simply is not re-forwarded anywhere. It is damped by the same `(1-DAMPING)`
    # teleport term as every other node, and accumulates real inflow from its dependents like
    # everyone else, but earns no extra retention bonus purely for having nothing left to
    # point to. `out_edges[i] == []` is the dangling marker `pagerank()` checks for below.
    return out_edges


def pagerank(tasks: List[Task], out_edges: Dict[str, List[Tuple[str, float]]],
             personalization: Dict[str, float]) -> Dict[str, float]:
    ids = [t.id for t in tasks]
    n = len(ids)
    if n == 0:
        return {}
    total_pers = sum(personalization.values()) or 1.0
    pers = {i: personalization.get(i, 0.0) / total_pers for i in ids}

    pr = dict(pers)
    for _ in range(MAX_ITER):
        new_pr = {i: (1.0 - DAMPING) * pers[i] for i in ids}
        # Dangling nodes (out_edges == []) intentionally do not redistribute their mass —
        # see the docstring in build_graph for why both usual conventions were rejected here.
        for i in ids:
            edges = out_edges.get(i) or []
            if not edges:
                continue
            total_w = sum(w for _, w in edges)
            if total_w <= 0:
                continue
            share = pr[i] / total_w
            for tgt, w in edges:
                new_pr[tgt] += DAMPING * share * w
        diff = sum(abs(new_pr[i] - pr[i]) for i in ids)
        pr = new_pr
        if diff < CONVERGENCE_TOL:
            break
    return pr


def dependents_of(tasks: List[Task], tid: str) -> List[Task]:
    return [t for t in tasks if tid in t.after]


def main():
    parser = argparse.ArgumentParser(description="Leverage-ranked task frontier for gasm's docs/tasks/*.md")
    parser.add_argument("--all", action="store_true", help="full ranking of every task, not just the frontier")
    parser.add_argument("--track", default=None, help="filter to a single track (e.g. trust-core, proof-arch, networking, graphics, perf, build-scale, debt-intake)")
    parser.add_argument("--json", action="store_true", help="machine-readable JSON output")
    parser.add_argument("--validate", action="store_true", help="run validation only; no ranking output")
    args = parser.parse_args()

    tasks, parse_errors = load_tasks()
    errors = validate(tasks, parse_errors)

    if errors:
        print("=" * 70)
        print(" gasm Task Frontier — VALIDATION FAILED")
        print("=" * 70)
        for e in errors:
            print(f"[!] {e}")
        print(f"\n{len(errors)} error(s). Fix docs/tasks/*.md frontmatter and re-run.")
        sys.exit(1)

    if args.validate:
        print(f"[+] {len(tasks)} task files parsed and validated OK (docs/tasks/*.md).")
        sys.exit(0)

    now = datetime.now(timezone.utc)
    eff = {t.id: effective_priority(t, now) for t in tasks}
    out_edges = build_graph(tasks)
    pr = pagerank(tasks, out_edges, personalization=eff)

    by_id = {t.id: t for t in tasks}
    done_ids = {t.id for t in tasks if t.status == "done"}

    if args.track:
        tasks_view = [t for t in tasks if t.track == args.track]
    else:
        tasks_view = tasks

    def leverage_pct(tid: str) -> float:
        return pr.get(tid, 0.0) * 100.0

    def task_row(t: Task) -> Dict:
        return {
            "id": t.id,
            "title": t.title,
            "status": t.status,
            "track": t.track,
            "priority": float(t.priority),
            "effective_priority": round(eff[t.id], 3),
            "leverage": round(leverage_pct(t.id), 4),
        }

    if args.all:
        ranked = sorted(tasks_view, key=lambda t: pr.get(t.id, 0.0), reverse=True)
        if args.json:
            print(json.dumps({"all": [task_row(t) for t in ranked]}, indent=2))
            return
        print("=" * 100)
        print(" gasm Task Frontier — FULL RANKING" + (f" (track={args.track})" if args.track else ""))
        print("=" * 100)
        print(f"{'#':>3}  {'id':<5} {'status':<14} {'track':<12} {'prio':>6} {'eff.prio':>9} {'leverage':>9}  title")
        for i, t in enumerate(ranked, start=1):
            print(f"{i:>3}  {t.id:<5} {t.status:<14} {t.track:<12} {float(t.priority):>6.1f} "
                  f"{eff[t.id]:>9.2f} {leverage_pct(t.id):>9.4f}  {t.title[:70]}")
        return

    # Default: frontier view.
    frontier = [
        t for t in tasks_view
        if t.status in ACTIONABLE_STATUSES and all(a in done_ids for a in t.after)
    ]
    frontier.sort(key=lambda t: pr.get(t.id, 0.0), reverse=True)

    non_frontier = [
        t for t in tasks_view
        if t.status != "done" and t not in frontier
    ]
    non_frontier.sort(key=lambda t: pr.get(t.id, 0.0), reverse=True)
    blocked_high_leverage = non_frontier[:8]

    if args.json:
        out = {
            "frontier": [],
            "blocked_high_leverage": [],
        }
        for t in frontier:
            row = task_row(t)
            deps = sorted(dependents_of(tasks, t.id), key=lambda d: pr.get(d.id, 0.0), reverse=True)[:3]
            row["unblocks"] = [d.id for d in deps]
            out["frontier"].append(row)
        for t in blocked_high_leverage:
            row = task_row(t)
            unmet = [a for a in t.after if a not in done_ids]
            row["unmet_deps"] = unmet
            row["blocked_on"] = t.blocked_on
            out["blocked_high_leverage"].append(row)
        print(json.dumps(out, indent=2))
        return

    print("=" * 100)
    print(" gasm Task Frontier — ready-now tasks ranked by leverage" + (f" (track={args.track})" if args.track else ""))
    print("=" * 100)
    print(f"{'#':>3}  {'id':<5} {'status':<14} {'prio':>6} {'eff.prio':>9} {'leverage':>9}  {'track':<12} title")
    for i, t in enumerate(frontier, start=1):
        deps = sorted(dependents_of(tasks, t.id), key=lambda d: pr.get(d.id, 0.0), reverse=True)[:3]
        unblocks = ", ".join(d.id for d in deps) if deps else "-"
        print(f"{i:>3}  {t.id:<5} {t.status:<14} {float(t.priority):>6.1f} {eff[t.id]:>9.2f} "
              f"{leverage_pct(t.id):>9.4f}  {t.track:<12} {t.title[:60]}")
        print(f"       unblocks: {unblocks}")

    if blocked_high_leverage:
        print()
        print("-" * 100)
        print(" Blocked high-leverage (hurry these prerequisites along):")
        print("-" * 100)
        for t in blocked_high_leverage:
            unmet = [a for a in t.after if a not in done_ids]
            reason = f"unmet after: {', '.join(unmet)}" if unmet else (
                f"blocked_on: {t.blocked_on}" if t.blocked_on else f"status: {t.status}"
            )
            print(f"     {t.id:<5} lev={leverage_pct(t.id):>7.4f}  prio={float(t.priority):>4.1f}  "
                  f"eff={eff[t.id]:>6.2f}  {t.title[:55]}")
            print(f"           gated by: {reason}")


if __name__ == "__main__":
    main()
