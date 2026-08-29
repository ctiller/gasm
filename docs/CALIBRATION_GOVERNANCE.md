# Calibration Data Governance — the Third Reference Class

> This is `docs/REVIEW.md` **Law 14 (Calibration Data Governance — The Third Reference
> Class)'s Law-5 design document** — Law 14 has been ratified by the repository owner
> (quoted in full in §1 and again in §13) and this document is the concrete mechanism
> for the performance-calibration work tracked in `docs/ROADMAP.md` §5. Status:
> **partially implemented** — `HardwareTimingHarness.lean` and
> `PerfHardwareFuzzer.lean` produce provisional schema-v2 artifacts under
> `calibration/x86_64/`. The acceptance-grade `scripts/check_calibration.py`
> binding/staleness gate, generated coefficient binding, and its Pillar-1 registration
> remain unimplemented; until those land, the checked-in artifacts are measurements,
> not accepted model coefficients.
> §13 states, requirement by requirement, which parts of this design are Law 14's own
> text (must trace to the quoted clause) and which are this document's own elaboration
> — the concrete field names, mechanisms, and schema that make an intentionally terse
> law checkable, which is exactly what a Law-5 design document exists to add. This
> revision responds to three rounds of design review: a **REDESIGN (scoped)** verdict on
> the first draft, a second cycle's two rulings (an arbitration on §11's uop-count
> question, and — since superseded — pulling Law 14 back to proposal status), and this
> cycle's ratification, which promotes that same text from proposal to citation
> throughout. §16 and §17 record the history.

## 0. What problem this solves

`docs/REVIEW.md` Law 4 governs *authoritative external text* — Intel/AMD manuals, the
PE/COFF spec, Win32 contracts: things this project did not author and must cite as
genuine ground truth. Law 6 keeps those citations honest through hash-pinned entries in
`references.json` and the local verified cache managed by
`scripts/check_references.py`; the authoritative prose itself is not committed.

Measured calibration data — an RDTSC median for a specific kernel on a specific CPU
under a specific turbo policy — is neither of those things. It is not vendored (nobody
publishes "the cycle count for `SHL r64, CL` on *this* i9-13900H"); it is not invented
either, or it would be exactly the "massive cheat" Law 4 forbids. It is **measured by
this project, from a harness this project owns, against hardware this project
possesses.** `docs/VISION.md` §5 states the target end-state plainly: "measured
calibration data is governed like `references/` — checked in, regenerable, never
hand-edited." The predecessor's failure explains why this needs its own design rather than
riding on Law 4/6 as written: **wsc died of exactly this gap** —
RDTSC medians were hand-transcribed as bare `Nat` literals into `Main.lean` and left to
rot (visibly stale: scalar and SIMD Mandelbrot both recorded as "8 cycles"), with no
harness checked in next to them and nothing that could tell a reader the numbers were
even still plausible.

**The design-review verdict on this document's first draft was blunt and correct: "a
design that reads well and would not have caught wsc."** wsc's actual failure had three
components — (1) a number was typed into source disconnected from its measurement, (2)
the thing that would have caught drift (a git-log check on one file) either wouldn't
have fired or would have fired on everything, and (3) nobody ever demonstrated the gate
would reject a bad file before trusting it passed good ones. Every mandatory fix below
exists to close one of those three gaps concretely, not just describe them.

## 1. Location and format

**Decision: a new top-level `calibration/` directory, not `references/calibration/`.**
This conclusion is unchanged from the prior draft; the reasoning is corrected below.

### Why not under `references/` — the textual argument

An earlier draft reasoned from the now-retired vendored-reference pipeline. That mechanism is no
longer current: external authoritative sources are metadata entries in `references.json`, and
their bytes live only in a gitignored verified cache. The durable distinction is still the source
of truth. Law 6 entries name material independently published upstream and reproducible by
re-fetching exactly those pinned bytes. Calibration data has no upstream publisher: a value such
as an RDTSC median for one kernel on one CPU is produced by this project's own committed harness
on stated hardware. Putting it in the reference registry would require a fabricated upstream URL
or blur two different reproducibility obligations. The top-level `calibration/` directory keeps
“re-fetch the authoritative source” (Law 6) separate from “re-run the owned harness under recorded
conditions” (Law 14 and this document).

### This gap between laws is closed — Law 14, ratified

A third top-level, checked-in, governed directory that is neither `docs/` (Law 1-3, 5)
nor `references/` (Law 4, 6) would otherwise be a real gap in `docs/REVIEW.md`'s
numbering. **This is now closed: the repository owner has ratified Law 14 (Calibration
Data Governance — The Third Reference Class) in `docs/REVIEW.md`, ending exactly where
this section's own reasoning above pointed** — a new numbered law rather than a stretch
of Law 6's text, because Law 6 binds `references/` by name and requires upstream
reproducibility, and measured data has no upstream. Quoted in full:

> ### Law 14: Calibration Data Governance (The Third Reference Class)
> **Measured data about this machine — timings, bandwidths, latencies, and any
> coefficient derived from them — is governed as a third reference class, distinct from
> Law 4's vendored specifications and Law 6's upstream-reproducible corpora. It MUST be
> checked in, regenerable by a committed harness, provenance-stamped, and never
> hand-edited; a model coefficient MUST cite its calibration file rather than carry a
> bare literal.**
>
> - **Why a third class**: Law 4 governs authoritative text we did not write; Law 6
>   binds `references/` by name and requires reproducibility *from an upstream*.
>   Measurement has no upstream — it is reproducible only by re-running a harness on
>   stated hardware — so calibration data satisfies neither law and would otherwise sit
>   in a gap between them.
> - **The failure being prevented is documented history**: this project's predecessor
>   recorded RDTSC medians as hand-transcribed `Nat` literals in source, which then
>   rotted silently (two different kernels frozen at the same measured value). Every
>   requirement below exists to make that specific rot detectable.
> - **Regenerable, not transcribed**: every calibration artifact is paired with the
>   committed harness that produces it, and its provenance records the harness commit.
>   Hand-editing a measured value is prohibited and must be *mechanically detected*, not
>   merely discouraged: artifacts store raw samples plus a committed pure reduction
>   function, and the gate recomputes the reduction and fails on mismatch.
> - **Provenance is mandatory and machine-checkable**: named device profile, host
>   fingerprint, frequency/power policy, OS build, tool versions, run conditions, and the
>   outcomes of the session's control vectors (Law 13) are recorded *in the artifact*. A
>   file that cannot show its controls ran is not evidence.
> - **Staleness is keyed on the measured subject**, not on one file's history: freshness
>   is a function of the harness's transitive source closure and an explicit list of
>   what was measured. A calibration file whose subject changed is stale even if the
>   harness did not.
> - **Recalibration is an explicit re-baseline**: artifacts carry a generation identity,
>   and consumers record the generation they were authored against, so a new measurement
>   cannot silently re-evaluate existing cost contracts.
> - **Coefficients cite, they do not copy**: a model constant traceable to measurement
>   must be bound to its calibration artifact by a mechanical check; a bare literal with
>   a prose citation is the prohibited shape.
> - **Honesty in output**: gate and report output states how many microarchitectures a
>   model has actually been validated on, and coefficients validated by neither a
>   vendored source nor a discriminating measurement are marked model-internal and may
>   not be cited as facts.
> - **Gate**: `python scripts/check_calibration.py`, registered in §4.1 Pillar 1.

**Every clause of this document from here on is written as an elaboration of one of
these ratified requirements, or is flagged explicitly as additional design detail this
document adds to make an intentionally terse law checkable — §13 carries the full
requirement-by-requirement traceability, in the same spirit as Law 1's discipline for
Lean declarations (nothing here should introduce a governance concept the law's own text
does not motivate, without saying so plainly).** The Pillar-1 gate registration Law 14's
own text points at ("registered in §4.1 Pillar 1") is not yet present in `docs/REVIEW.md`
as of this document's authoring — this document does not add it, deliberately: three
agents currently edit that file, and landing it is left to the owner/coordinator to do
centrally rather than risk a conflicting edit.

### The `check_refs.py` consequence — land the fix now, standalone

`scripts/check_refs.py`'s `DOC_DIRS = [REPO_ROOT/"docs", REPO_ROOT/"references"]` is
what makes a path citable at all: only markdown files under those two roots get their
headings indexed, and only entries in that index make a `/- REF: ... -/` anchor
resolvable. Because `calibration/` sits outside both entries, a markdown stub placed
there is invisible to `check_refs.py` until the tool is extended.

**Disposition: land `DOC_DIRS = [..., REPO_ROOT/"calibration"]` now, as its own
standalone one-line change, not bundled with F3's first calibration file.** With
`calibration/` empty (or nonexistent), `Path.glob` on a missing/empty directory finds no
markdown files and the change is a verified no-op — safe to land immediately and get out
of F3's critical path entirely, rather than risk F3 discovering the citation path
doesn't work mid-task.

### File format — CSV is not a lower-effort escape from §6's binding, it is a different tier

The prior draft's §5 rejected a bare SHA-256-over-the-file hand-edit check as "defeated
by anyone willing to also update the hash by hand," then its own §1 applied exactly that
control — a `.meta.json` sidecar hash over the CSV bytes — as the *sole* protection for
every E1/E3/E4 sweep file (PCIe, storage, network). That is not a format detail, it is
governing an entire measurement class at a materially weaker tier than everything else
in this document while implying uniformity. Two fixes, and the design must pick one
per-file rather than leave it ambiguous:

- **Primary requirement: per-cell raw retention.** A CSV sweep row (one `(size,
  direction)` cell for E1, one `(block_size, queue_depth)` cell for E3, etc.) is
  accompanied by the same `raw_samples` array §6 requires for a scalar cycle
  measurement, either inline (a JSON array-of-objects is in fact tractable here — a
  sweep with, say, 20 sizes × 2 directions × 200 samples/cell is 8,000 numbers, not an
  unreasonable file) or as a per-cell raw-samples file under a `raw/` subdirectory next
  to the summary CSV, referenced by a stable cell key. Either way, `check_calibration.py`
  recomputes each cell's summary statistic from its own raw samples exactly as it does
  for a scalar JSON file (§6) — no weaker tier, just a table-shaped container for the
  same mechanism.
- **Explicit fallback: a declared weaker tier.** If per-cell raw retention turns out to
  be genuinely impractical for a specific sweep shape (this document does not have
  E1/E3/E4 hardware in front of it to know that yet), the calibration file's provenance
  MUST carry a literal `"integrity_tier": "hash-only"` field, and any consumer citing it
  (§6's binding, F4's cost functions) must surface that tier string wherever the
  coefficient is used — never let a hash-only-tier file look identical to a fully
  recomputation-checked one. This is the mechanized version of "state explicitly rather
  than imply uniformity."

Markdown is never a data format — see §6 for what the citation stub may and may not
contain.

### Directory layout

```
calibration/
  x86_64/
    shl_by_cl.json
    shl_by_cl.md              # REF-citable stub, see §6 — contains zero numbers
    div_r64.json
    div_r64.md
    timer_overhead.json       # the calibration-pass constant §5 depends on
    timer_overhead.md
  transport/
    pcie_h2d_d2h.csv
    pcie_h2d_d2h.meta.json
    pcie_h2d_d2h.md
  storage/
    fio_sweep.csv
    fio_sweep.meta.json
    fio_sweep.md
  network/
    loopback_sweep.csv
    loopback_sweep.meta.json
    loopback_sweep.md
```

Two changes from the prior draft's layout, both closing minor findings:

- **No `<profile-name>/` subdirectory.** The prior layout nested files under
  `x86_64/goldenCove/`, which puts the profile name in two places — the directory path
  and the `device_profile` JSON field — with no rule for which wins if they disagree
  (an unlinked-twin pattern, Law 12). **`device_profile` inside the JSON is the only
  place profile identity lives; the gate never reads a directory name to determine
  validity, only the field (checked, per §4, against what `Uop.lean` actually defines).**
  Directory/filename structure is human-navigation convenience only. If a file needs
  disambiguating by profile in its filename for a human browsing the tree (e.g. two
  profiles both calibrate `shl_by_cl`), name it `shl_by_cl__goldenCove.json` — a purely
  cosmetic convention the gate ignores.
- **No empty `skylake/`/`zen4/` placeholder directories.** Git cannot track an empty
  directory, and per §10, no calibration file for those profiles can exist today (T11:
  one physical machine). The tree above shows only what actually exists; a directory for
  a second microarchitecture appears organically the day a real calibration file for it
  is first generated, with no placeholder scaffolding required or committed in advance.

## 2. Provenance and run conditions

Every calibration JSON's `provenance` object is mandatory. Two sub-blocks: **identity**
(who/what/when produced this file) and **run conditions** (what state the machine was
actually in during this specific run — see §2.2, the part the prior draft missed
entirely).

### 2.1 Identity fields

| Field | Purpose |
| :-- | :-- |
| `device_profile` | Must name a `def <name>Profile : MicroarchProfile` that `Uop.lean` (or a future non-x86 target's equivalent) defines at the commit the gate runs against (§4 check 2). |
| `host_id` | An **opaque, project-assigned** identifier (e.g. `"machine-01"`), not a real hostname — resolving the prior draft's design-review question 1 in favor of anonymity. |
| `host_fingerprint` | A hash over stable, low-entropy hardware identifiers obtainable without external lookup (CPUID vendor string, family/model/stepping, logical core count). Anonymity is fine; unverifiability is not — `check_calibration.py` flags it when two files share a `host_id` but disagree on `host_fingerprint` (machine swapped without relabeling) or share a `host_fingerprint` under two different `host_id`s (the same machine double-counted as two, silently inflating the §10 validated-microarchitecture count). A mismatch is flagged for human reconciliation, not auto-resolved. |
| `os_build` | Full OS version string. |
| `tool_versions` | Every tool whose behavior could shift the numbers (Lean, NASM, Python for CSV-sweep harnesses) — the data-side half of `scripts/run_gates.py`'s oracle-version recording. |
| `iso_date` | ISO-8601 timestamp of the run. |
| `harness_path` | Repo-relative path to the harness's entry-point module (e.g. `Gasm/Targets/X86_64/HardwareHarness.lean`, or F1's `PerfHardwareFuzzer` CLI). |
| `harness_closure_hash` | See §4 — a hash over the harness's transitive dependency set, **not** a single-file git-log lookup. |
| `measured_subject` | See §4 — an explicit list of repo paths defining what this file's number is actually *about*, distinct from what merely produced it. |
| `harness_invocation` | The literal command line used, so a human can re-run it verbatim. |

### 2.2 Run conditions — what the prior draft omitted, and why it mattered

The design-review finding: the prior draft's `frequency_policy` used Linux vocabulary
(governor, turbo) on a Windows host, with `"if measurable"` quietly escaping the one
field that actually mattered, and named nothing about AC/battery, Windows power plan,
thermal state, core affinity, or **P-core vs. E-core placement** — on a hybrid
i9-13900H, the same kernel measured on an E-core is not noise around the same number, it
is a measurement of a *different microarchitecture* mislabeled as the profile it wasn't
run on. `run_conditions` is mandatory and per-run (not per-profile — see §2.3 for the
distinction that matters to F5):

```json
"run_conditions": {
  "power_source": "AC",
  "windows_power_plan": "High performance",
  "core_affinity": 4,
  "core_type": "P-core",
  "thermal_throttle_observed": false,
  "observed_clock_mhz_median": 4700,
  "concurrent_load_note": "other agent worktrees may build/test on this shared machine; no isolation guarantee"
}
```

### 2.3 The dispersion guard — needs no honesty at all

`run_conditions` is self-reported by the harness and, like any self-report, is only as
good as the harness's own instrumentation. The complementary, harness-independent check:
**every `raw_samples_cycles` array preserves run order**, and `check_calibration.py`
computes, at verification time, purely from the numbers themselves:

- **IQR/median ratio** — fails the file if dispersion exceeds a stated bound (catches
  background interference, SMI storms, unstable turbo).
- **First-half vs. second-half median drift** — fails the file if the first half of the
  run and the second half disagree beyond a stated bound (catches thermal ramp during
  the run and — explicitly relevant on a machine other agent worktrees build on
  concurrently — a background load that started or stopped partway through).

This requires nothing to be honestly reported; it is arithmetic over the data the file
already must carry, and it is the generation-time complement to §8's session-level
positive/negative controls.

### 2.4 Where a profile's clock/frequency provenance actually lives (resolving the F5 tension)

The composable-cost-view work in `docs/ROADMAP.md` §5 requires explicit conversions owned by
named device profiles (a profile owns its clock/frequency provenance) for the
cycles→µs architect view. `MicroarchProfile` (`Uop.lean:57-68`) has no clock/frequency
field today, and §2.2's `run_conditions.observed_clock_mhz_median` is per-run diagnostic
data — if two kernel measurements for the same profile record two different observed
clocks (plausible: turbo ramp differs run to run), there must be a rule for which one
F5's conversion function actually uses, or F5 inherits an ambiguity this document was
supposed to close.

**Resolution: frequency provenance for conversion purposes is itself a calibration
file, exactly one per profile, and it is canonical — not derived from any individual
kernel measurement's `run_conditions`.**

- `calibration/x86_64/goldenCove_clock_provenance.json` — its own harness (a dedicated
  clock-measurement pass, not incidental to a cycle-count kernel run), its own
  `raw_samples_cycles`/reduction/staleness lifecycle exactly as any other calibration
  file, producing the single number (or small parametric model, if turbo state needs
  more than one number) F5's conversion function reads.
- `MicroarchProfile` gains a new field, `clockProvenanceRef : String`, naming that
  file's path — a small, mechanical Lean-side addition this document specifies but does
  not implement (flagged as F5's responsibility to land, alongside the conversion
  function itself, since F2's design stage should not reach into `Uop.lean`).
- Individual kernel measurements' `run_conditions.observed_clock_mhz_median` remains
  purely diagnostic (feeds §2.3's dispersion guard, and is useful evidence if a
  measurement looks anomalous) — it is never read by the conversion layer, closing the
  two-files-disagree ambiguity by construction: there is exactly one authoritative
  source per profile, and every other file's clock observation is explicitly
  non-authoritative.

## 3. Regeneration and measurement identity

A calibration file is either produced directly by, or trivially re-producible by,
exactly the harness named in `provenance.harness_path` — there is no format that permits
"value derived from a harness run by hand elsewhere and typed in here." F1's
`PerfHardwareFuzzer`/`--hardware` CLI mode is the first concrete harness this mechanism
governs; the schema is harness-agnostic so it also covers F3's staged calibration and
E1/E3/E4's PCIe/storage/network sweeps. One harness may produce many calibration files;
the pairing is data → harness, not harness → data.

What "regenerable" means precisely — closure hash and measured subject — is specified in
§4, because in this document's revision they are inseparable from the staleness check
itself rather than a separate description of pairing.

## 4. Mechanical staleness gate — re-keyed

The prior draft's gate compared `provenance.harness_commit` against
`git log -1 --format=%H -- <harness_path>` for one file. The design-review finding: this
is simultaneously **too narrow** (the measured subject — a kernel definition in
`Shift.lean`, or the model surface in `Performance.lean`/`Uop.lean` that F3 stages 2-4
rewrite — is not in the drift set at all; change the kernel and leave the driver
untouched, every calibration file reports fresh) and **too coarse** (a comment edit in
`HardwareHarness.lean` invalidates every calibration file that names it at once). Under
mass invalidation, the cheapest path back to green becomes hand-editing
`harness_commit` in N files — which is not a hypothetical, the prior draft's own §5
*mandated* exactly that edit as a "complementary control." **That control is deleted in
this revision; it trained the forgery this whole document exists to prevent.**

`scripts/check_calibration.py` runs, per file:

1. **Closure-hash check.** `harness_closure_hash` (§2.1) is a hash over the harness
   module's transitive Lean import closure at generation time (concatenated git blob
   hashes of every file reachable from `harness_path`'s imports). The gate recomputes
   this closure hash against the current tree and fails if it differs — this correctly
   invalidates a calibration file when the harness or anything it imports has changed,
   including `Performance.lean`/`Uop.lean` edits that a single-file git-log check would
   have missed entirely.
2. **Measured-subject check.** `measured_subject` (§2.1) is an explicit, human-curated
   list of repo paths this specific file's number is *about* — e.g. `shl_by_cl.json`
   names `Gasm/Targets/X86_64/Instructions/Shift.lean` even if the kernel-generation
   logic technically routes through the harness's own import closure already; making it
   explicit means the dependency set is reviewable and auditable rather than "whatever
   the compiler happens to import this week," and it also lets a human flag a file as
   dependent on a model file (e.g. `Performance.lean`'s cost formula) that the harness
   itself does not import but that F4/F5 will read this number *through*. The gate
   applies the same closure-hash treatment to every path named here.
3. **Profile-existence check.** Unchanged from the prior draft: parse `Uop.lean` for
   `def <name>Profile : MicroarchProfile := {` declarations; fail if
   `provenance.device_profile` names one that doesn't exist.
4. **Discrimination control** (new — directly targets wsc's actual observed symptom,
   not just the mechanism that should have caught it). The calibration suite for a given
   measurement domain (x86 cycles, PCIe transfer, …) MUST contain at least one **named
   kernel/measurement pair that is required to differ** by more than a stated bound —
   e.g. a NOP-dominated loop versus a long dependent-ALU-chain loop, chosen so that no
   correctly functioning harness could plausibly measure them as equal. `wsc`'s failure
   ("scalar and SIMD Mandelbrot both 8 cycles") is precisely a case this control is
   built to catch: two kernels that must differ, measured identically, is evidence the
   harness itself is broken (stuck timer, wrong kernel dispatched, copy-paste in the
   test list) regardless of whether any individual file's own staleness/hand-edit checks
   pass. This runs at the *suite* level (across a session's files), not per-file, and a
   failing discrimination pair aborts trust in the entire session's output, not just the
   two files involved — see §8.

**On the accepted coarseness:** a closure-hash check still invalidates on a pure comment
edit, same as the discarded single-file check would have. This revision does not solve
that false-positive cost — doing so would need declaration-level (AST-aware, not
byte-content) hashing, which is real tooling investment this design doc does not scope.
The disposition is deliberate: **the only legitimate response to staleness is re-running
the harness**, even when the triggering change was cosmetic. This revision's fix is
removing the escape hatch that made false-positive churn *expensive enough to tempt
forgery*, not making the churn itself rarer. §14 names finer-grained hashing as an
explicit open question rather than claiming it's solved.

Per Law 13, this gate does not count as delivered on design alone. The F2
implementation stage's acceptance evidence is a demonstrated negative control (a file
failing each of checks 1-3 individually, plus a suite failing check 4) and a positive
control (a correct suite passing all four) — this design doc specifies what must be
exercised, not that it has been.

## 5. Reduction and the timer-overhead DAG

The prior draft's `reduction.method` said "timer-overhead subtracted" as prose with no
field carrying the actual constant — meaning the gate could not reproduce the stated
`median`/`min`/`max` from `raw_samples_cycles` at all, and the overhead constant became
exactly the kind of unrecorded free parameter this document exists to eliminate;
`docs/RDTSC_HARNESS.md` §6.4 hands this constant a name and explicitly requires it be governed as
calibration data,
which the prior draft did not act on.

**Fix: samples are stored *pre-subtraction*, and the overhead constant is itself a
calibration file, referenced by pointer:**

```json
{
  "schema_version": 2,
  "provenance": { "...": "as §2" },
  "raw_samples_cycles_unadjusted": [438, 434, 441, 435, 457, ...],
  "timer_overhead_ref": "calibration/x86_64/timer_overhead.json",
  "reduction": {
    "method": "median-of-N over raw_samples_cycles_unadjusted, minus
               timer_overhead_ref's own current median (not mean — SMI/interrupt tail
               outliers), after 5k-20k warmup iterations to stabilize turbo/cache state",
    "median": 409,
    "min": 402,
    "max": 431
  }
}
```

`timer_overhead.json` is a calibration file like any other — its own `provenance`,
`raw_samples_cycles_unadjusted` (a pure CPUID+RDTSCP bracket around nothing), its own
staleness lifecycle. **This makes `calibration/` a small DAG, not a flat set of files**:
`shl_by_cl.json` depends on `timer_overhead.json` the same way it depends on the
harness. `check_calibration.py` extends accordingly: a file whose `timer_overhead_ref`
target is itself stale (fails its own §4 checks) is transitively stale, and the gate
reports the dependency chain rather than a bare pass/fail, so a human sees *why*
(`shl_by_cl.json is stale because timer_overhead.json is stale because its harness
closure changed`) instead of chasing an opaque failure.

The prior draft's `reduction.method` also invented a "top/bottom 1% trimmed" step
attributed loosely to "the wsc technique" — the historical predecessor reconstruction names CPUID+RDTSCP
bracketing, median-of-N (explicitly not mean), a separate subtracted overhead pass, and
5k-20k warmup iterations; it does not mention trimming. That invented step is removed
above; a real trimming policy may be added later, but only once actually adopted by a
harness and named honestly as this project's own choice, not attributed to a source that
didn't specify it — a document whose entire thesis is "numbers must trace to where they
came from" cannot itself contain an untraceable methodological detail.

## 6. Citation, and mechanically binding the coefficient to the value (Law 12)

This is the most serious hole the design review found, and it's worth stating why
plainly: **the prior draft's citation mechanism only checked that a markdown heading
exists — nothing compared the Lean literal `shlByClUopCount := 3` to
`reduction.median`.** Recalibrate the file, get a fresh, self-consistent,
correctly-provenanced JSON that changes the median from 3 to something else, and the
Lean literal, the anchor, and the build all stay green while the model silently
predicts the old number forever. That is wsc's literal-rot, wearing a provenance header.
It is also, independently, an unnoticed Law 12 violation: the JSON's `reduction.median`,
the Lean `def`, and (in the prior draft's own worked example) a *third* restatement of
the number in the stub's prose are three unlinked encodings of one fact.

**Fix, in two parts:**

### 6.1 Strip every number from the citation stub

`calibration/x86_64/shl_by_cl.md` — the markdown file `/- REF: ... -/` actually points
at, per §1's `DOC_DIRS` fix — contains **zero numeric measurement values**. Prose only:
what was measured, a pointer to the JSON, the regeneration command.

```markdown
# SHL r64, CL — cycle-measurement evidence (Golden Cove)

RDTSC cycle measurements against `goldenCoveProfile`, including the discriminating-pair
containment result (§11) this file's calibration currently rests on. Raw samples,
provenance, and the current reduced value live in `calibration/x86_64/shl_by_cl.json` —
this stub restates none of them (§6.1), so there is exactly one place the number can be
read from. Regenerate via
`PerfHardwareFuzzerCLI --hardware --kernel shl_by_cl --profile goldenCove`.
```

### 6.2 A mechanical `bindings` entry — the coefficient is compared, not merely cited

Every calibration JSON carries a `bindings` array naming exactly which Lean
declarations are derived from which of its fields:

```json
"bindings": [
  { "lean_file": "Gasm/Targets/X86_64/Instructions/Shift.lean",
    "decl_name": "shlByClUopCount",
    "reduction_field": "median" }
]
```

`check_calibration.py` parses `lean_file` for `decl_name`'s literal value (the same
declaration-locating technique `check_refs.py`'s `LEAN_DECL_REGEX` already uses) and
fails the build if it does not equal the named `reduction` field's *current* value.
Recalibration that changes `reduction.median` now fails the build at the binding check,
immediately and specifically — not silently, and not merely because the file's own
staleness fields disagree with git history.

**Where a build-time comparison is possible, generation is strictly preferred over
comparison (Law 13's own preference order: unrepresentable-by-construction beats a
linter).** For a scalar coefficient with no downstream Lean computation depending on its
literal form, `check_calibration.py` should instead *emit* the Lean constant from the
JSON at build time (a single generated file, e.g.
`Gasm/Targets/X86_64/Instructions/Shift.generated.lean`, imported by `Shift.lean`) so
there is exactly one source and no comparison to keep in sync at all. The `bindings`
comparison mechanism above is the fallback for coefficients that are hand-authored
inline for readability or composed with other hand-written logic where generation isn't
a clean fit — both paths are specified here; which one a given coefficient uses is a
per-declaration authoring choice, not a global switch.

This directly closes a requirement of the parametric-cost-function work in
`docs/ROADMAP.md` §5: do not let coefficients re-enter the codebase as
bare literals with no calibration citation, which would silently undo F2's governance
mechanism at one remove — §6.2 is the concrete mechanism that requirement needs.

## 7. Hand-edit prohibition, restated

Unchanged core mechanism from the prior draft, now correctly load-bearing because of
§6: raw samples stored in full (`raw_samples_cycles_unadjusted`, §5), `reduction`
recomputed by `check_calibration.py` from those samples using the named method, and now
also compared against the Lean literal it's bound to (§6.2) — so hand-typing a
"corrected" number requires forging a self-consistent raw-sample array *and* the
recalibration must still pass the discrimination control (§4 check 4) and dispersion guard
(§2.3), each independently checking a different property of the same underlying data.

**Explicit residual:** this is still not cryptographic non-repudiation — a sufficiently
determined actor could forge a self-consistent raw array satisfying all of the above.
That residual is accepted, not solved, and is not treated as this document's biggest
open risk (see §14 and the coordinator's disposition on the prior draft's question 6:
the actual risk was the discarded bump-control training casual forgery, not a
theoretical sophisticated one).

## 8. Recording controls in the file, and the harness-side pattern to copy

The prior draft specified session-level positive/negative controls and an
abort-on-absent-device rule in prose, then noted nothing records whether they actually
ran — a file produced with controls disabled is byte-identical to one produced with them
enabled, which under Law 13 means the controls, as specified, don't count as delivered
and *can't even be checked after the fact*.

**Fix: `provenance.controls` is mandatory and records outcomes, not just intent:**

```json
"controls": {
  "positive_control_kernel": "nop_loop",
  "positive_control_measured_cycles": 4,
  "positive_control_band": [1, 10],
  "negative_control_input": "div_by_zero_kernel",
  "negative_control_observed": "rejected: #DE fault, excluded from sample set",
  "device_identity_check": "CPUID leaf 0x1 matches goldenCoveProfile signature",
  "discrimination_pair": ["nop_loop", "long_dependent_chain"],
  "discrimination_pair_values": [4, 812],
  "discrimination_pair_min_delta_required": 50
}
```

`check_calibration.py` fails a file lacking this block outright, and independently fails
it if `positive_control_measured_cycles` falls outside `positive_control_band` or the
discrimination pair's recorded delta is below its required minimum — the file is not
merely claiming controls were run, the gate re-checks the claim against the recorded
numbers.

**Harness-side requirement: callee-enforced, type-level fail-closed — name the existing
patterns to copy, don't reinvent.** This project already has exactly the right shape in
two places, and the harness extension this document depends on (F1) should copy them
rather than invent a third convention:

- `Gasm/Targets/Wasm/SemanticsFuzzer.lean`'s `ensureOracleControlsRan` — a
  memoized, once-per-process control run that every entry point (including a caller
  invoking a single case directly, bypassing the top-level suite runner) calls itself,
  so there is no code path that reaches a measurement without the controls having run
  first, regardless of which function a caller invokes.
- `Gasm/Targets/X86_64/HardwareHarness.lean`'s `runHardwareBatch` — returns
  `IO (Except String (List HardwareExecutionResult))`, structurally preventing a
  fail-open harness: every failure mode (spawn failure, abnormal exit, short/garbled
  output) routes through `Except.error`, and there is no code path left that fabricates
  a success-shaped result. F1's timing extension should return calibration results
  through the same `Except`-typed shape — a calibration file is producible only from the
  `.ok` branch of a real batch run, never synthesized on a control failure or harness
  error.

## 9. External tables (Agner Fog / uops.info) — licensing determination

**Determination, unchanged: cite by reference, do not vendor either corpus's tables
under Law 4. Self-measured calibration is primary; external tables are cross-checks
only, never the source of a shipped coefficient.**

The prior draft argued this from a specific claimed reading of Agner Fog's
redistribution terms (whole-document-only, no excerpting) that this design doc has not
independently vendored or verified — restating that claim as the load-bearing reason
would make the determination only as solid as an uncited license reading might turn out
to be wrong. **The determination should hold regardless of exactly what either license
says**, for two independent reasons that don't depend on it:

- **This project's own measurements are the more relevant ground truth regardless of
  what an external table's license permits.** Agner Fog's and uops.info's published
  figures describe *different physical chips* than the one this repo measures against
  (T11: one i9-13900H). A permissively licensed table for a different microarchitecture
  is still not "ground truth for this repo's model" the way a vendored SDM chapter is
  ground truth for an encoding — it is at best corroborating evidence for a
  cross-check, which is exactly the role this determination already assigns it.
- **No vendoring decision can be made responsibly without an actual license reading**,
  and this document does not have one. Absent that, the only defensible default is the
  one that requires no license risk at all: cite by reference in prose (e.g. a task or
  ADR noting "our measured figure is broadly consistent with Agner Fog's published
  table for a comparable microarchitecture"), never encode their tables into
  `calibration/` or `references/` as data.

If a future author obtains an actual, read, written determination of either source's
terms — permissive enough to vendor, or specific permission granted — that determination
supersedes this section; this section is deliberately not staking the conclusion on a
license claim nobody here has verified.

## 10. Multi-profile honesty, mechanized

The prior draft's mechanism for "don't imply validation that doesn't exist" was prose:
"any report or ADR citing them must say so." Law 13 requires construction, not a
prose reminder a future author can simply forget to write — a cost function can select
`skylakeProfile` today and hand back a plain `Nat`/`PerfCycleBounds` with nothing marking
it as unvalidated.

**Fix — a status tag threaded through the type, not just the gate's console output:**

```lean
inductive CalibrationStatus where
  | siliconValidated      -- at least one non-stale calibration file exists for this profile
  | siliconUnvalidated    -- profile is defined, but no calibration file has ever targeted it
  | syntheticBound        -- profile is not physical silicon at all (idealProfile)
```

A cost-producing function returns a small wrapper, `CalibratedCost`, pairing the
computed `PerfCycleBounds` with the `CalibrationStatus` of the profile it was computed
under. **The honesty-drop becomes an explicit, greppable act**: only
`CalibratedCost.assertSiliconValidated` unwraps to a bare value silently; every other
path (`.acceptUnvalidatedWithJustification "..."`, say) requires the caller to write
down why it's accepting an unvalidated number, so a report or contract that does this
is reviewable, not silent.

**`idealProfile` is a category error under "non-load-bearing until measured," not an
instance of it.** It is deliberately synthetic — a 1-cycle deductive bound for
formal reasoning, never intended to correspond to any silicon — so it can never earn
`siliconValidated` and should never be reported as "not yet validated" (implying
measurement is pending) either; it gets `syntheticBound` as its own permanent category,
distinct from `skylakeProfile`/`zen4Profile`'s `siliconUnvalidated` (which *could* earn
validation the day a second machine exists). The current remedy for dead fields
(`reciprocalThroughput`, `renameWidthUops`, etc.) is deleting those *fields* — a
separate concern from this section, which is about tagging *profiles*, and this
document does not recommend deleting any profile.

**The disclosure string surfaces in two places, not one:** `check_calibration.py`'s
summary output states "validated on exactly N microarchitectures" (N = count of
profiles with `siliconValidated` status) as the prior draft specified, **and** the same
string is added to `PerfFuzzerCLI`'s own output — the vacuity concern recorded in
the relevant vacuity risk is specifically a CLI printing a clean success with no such disclosure, so the
disclosure belongs where that vacuity actually lives, not only in a separate lint tool a
reader might not run.

## 11. Uop counts are model-internal parameters, not observables — arbitrated

**Ruling (this cycle): no PMU path is scoped into F1. This section is resolved, not
flagged.** The previous revision framed this as "RDTSC cannot measure uop counts" and
treated that as a concession requiring a PMU escape hatch. That framing conceded too
much. **Uop counts are not observables at all — they are internal parameters of the
cost model.** The observable this project actually has, and the only one that matters
operationally, is time: RDTSC measures cycles, and cycles are exactly what
`computeCycleBounds`'s containment criterion (F1) checks. A wrong uop-count assumption
is not invisible to that observable — it is *exactly* the kind of thing a cycle
measurement exposes: if `SHL r64,CL` is really 3 uops and the model assumes 1, that
mismatch shows up as a containment or rank-order failure on a shift-heavy kernel,
which RDTSC measures fine, no counter access required.

Rejecting a PMU path is also the right call independent of the reframing: a
Windows performance-counter path means a signed kernel driver or a VTune/Intel-PCM-style
dependency — a large scope expansion, a new permanent TCB entry, and platform lock-in
that no current spike demands (`docs/DECISIONS.md` §1: models grow only on demand, never
speculatively). The two named coefficient defects (`SHL r64,CL` at 1 uop vs. a real 3; `DIV r64` at 5
uops vs. a real ~36) do not need a counter to close — they need the right *shape* of
cycle-measurement evidence, specified below.

### The F1/F3 interface, specified precisely

**F3 stage 1 is retitled, in substance not just in name: "derive coefficient
corrections from cycle measurements on discriminating kernel pairs," not "measure uop
counts."** A **discriminating kernel pair** is two kernels whose model-predicted
*ranking* flips depending on whether a specific coefficient is correct — e.g. if the
model assumes `SHL r64,CL` is 1 uop, a kernel dominated by CL-shifts on a
narrow-port-eligibility instruction should rank *faster* than a kernel with equivalent
port pressure from wider-eligibility ops; if the real uop count is 3, that ranking
should flip or collapse under real hardware. Constructing such a pair and checking
whether real RDTSC measurements agree with the model's prediction is a direct
application of mutation testing to the perf model itself — the same shape as the
"executes ≠ discriminates" trust finding for the correctness fuzzers, and the same shape
as §4's discrimination control already added against wsc's symptom (two things that must
differ, checked to actually differ). A coefficient correction derived this way is a real
measurement-backed correction, not a guess — it just never required reading a counter to
get there.

### What this means for §9's citation rule and §10's status tag

§9 already states self-measured calibration is primary and external tables are
cross-checks only; this section adds the missing third case a coefficient can be in,
and makes it mechanically distinguishable rather than silently defaulting to "looks
calibrated": **any uop-count-class (or other model-internal-parameter) coefficient
claim must trace to either (a) a vendored authoritative source (Law 4 — an actual
Optimization Manual/uops.info citation, if §9's licensing posture is ever revisited), or
(b) a discriminating-kernel cycle measurement of the shape above. A coefficient with
neither is marked `modelInternalUnvalidated` and MUST NOT be cited, in a report or
code comment, as a measured fact** — it is an invented placeholder exactly like `SHL`'s
current `1 uop` and `DIV`'s current `5 uops`, and this tag is what keeps that honestly
visible rather than looking calibrated because a calibration file happens to exist for
it.

`§10`'s `CalibrationStatus` inductive gains this as its fourth constructor, replacing the
prior revision's `hypothesisIndirectlyValidated` naming (which still implied a counter
was the missing ingredient) with language that matches the reframing:

```lean
inductive CalibrationStatus where
  | siliconValidated       -- backed by a real cycles-class RDTSC measurement
  | siliconUnvalidated     -- profile defined, no calibration file targets it yet
  | syntheticBound         -- idealProfile — not physical silicon, never measured
  | modelInternalUnvalidated -- e.g. a uop-count assumption with no discriminating-
                              -- kernel measurement and no vendored source behind it
```

A `modelInternalUnvalidated` coefficient can be *promoted* to `siliconValidated` the
moment a discriminating-kernel pair is constructed and passes containment against it —
at that point it is no longer "invented," it is a real cycle-measurement-backed
correction, and the calibration file recording that promotion cites the discriminating
pair's kernel definitions and containment result directly (§8's `discrimination_pair`
fields are exactly the right shape to reuse here, generalized from a suite-sanity check
to a coefficient-validation record).

This closes the recorded coefficient defect without a PMU and without "the coefficient stays invented"
as a silent, undocumented outcome — the outcome is instead an explicit, checkable tag
that is either promoted by real evidence or stays honestly marked as unvalidated.

## 12. Versioning and re-baseline (generation identity) — new section

Neither draft addressed this until the design review raised it: `schema_version`
versions the *schema*, not the *data*. F4 makes cost contracts build-failing against
their stated bound: a routine whose actual measured/derived cost exceeds its contract's
stated cost function must fail a
build gate"). Without an explicit generation concept, one recalibration (§6 correctly
making the build fail on a stale binding) resolves by simply updating the Lean literal
to the new number — silently re-baselining every downstream cost contract's budget in
the same commit, with no record that a re-baseline event (as opposed to a genuine
regression) is what happened. Both F4 and F5 defer this question to F2 explicitly.

**Fix: generation identity is the calibration file's own content hash at the moment a
contract is authored against it, recorded on the contract, not on the calibration file.**

- A cost contract (F4's authoring surface) carries, alongside its `/- REF: -/`
  citation, an explicit generation stamp: `-- CALIBRATION_GENERATION: <blob-hash-of-the-
  cited-JSON-file-at-authoring-time>`.
- `check_calibration.py` (or a linter alongside it) compares the recorded generation
  hash against the calibration file's *current* blob hash. A mismatch means
  recalibration happened since the contract was authored — this is reported distinctly
  from "the bound was exceeded": it is **"this contract's coefficient is stale relative
  to a re-baseline, requires explicit human re-derivation and a new
  `CALIBRATION_GENERATION` stamp,"** not an automatic silent pass-through of the new
  number and not an automatic build failure indistinguishable from a real regression.
- Landing a generation bump is therefore always a distinct, reviewable commit: the new
  blob hash, the (possibly unchanged, possibly updated) coefficient, and — if the
  contract's stated cost bound needs adjusting because of it — that adjustment, all
  together, so a reviewer sees "recalibration landed, here's what it changed" as one
  legible unit rather than an ordinary-looking diff to a `Nat` literal.

## 13. Law 14 traceability, and wiring the gate

### 13.1 Requirement-by-requirement traceability (Law 1 discipline applied to this doc)

Law 14 is deliberately terse — one paragraph plus seven bullets, ratified as governance,
not as a schema. This document is its Law-5 design: the table below maps every clause of
the ratified text (quoted in full in §1) to where this document turns it into a checkable
mechanism, and separates that from the parts of this document that are **this author's
own elaboration**, not text the law itself dictates — the concrete schema, field names,
and thresholds a terse law necessarily leaves open, made explicit rather than left to be
invented silently later by whoever implements `check_calibration.py`.

| Law 14 clause | This document's mechanism | Additional design detail beyond the law's own text |
| :-- | :-- | :-- |
| "checked in, regenerable by a committed harness... never hand-edited" | §3 (regeneration pairing), §7 (hand-edit prohibition) | `calibration/` directory layout, per-profile subdirectory convention (§1) |
| "distinct from Law 4... Law 6... satisfies neither" | §1 (location decision, gap argument) | none — this is the law's own stated reasoning, restated |
| "regenerable, not transcribed... raw samples plus a committed pure reduction function... recomputes... fails on mismatch" | §5 (timer-overhead DAG), §7 | the specific `raw_samples_cycles_unadjusted`/`timer_overhead_ref` field shapes; the DAG-of-calibration-files structure |
| "provenance is mandatory and machine-checkable: device profile, host fingerprint, frequency/power policy, OS build, tool versions, run conditions, control-vector outcomes" | §2 (identity + run conditions), §8 (recorded controls) | exact field names (`host_fingerprint`, `run_conditions.core_type`, etc.); the §2.3 dispersion guard, which is this document's own addition on top of what Law 14 requires (Law 14 does not mention dispersion — it is derived from Law 13's control-vector spirit, not from Law 14's text, and is flagged as such) |
| "staleness keyed on the measured subject... harness's transitive source closure and an explicit list of what was measured" | §4 (closure hash + `measured_subject`) | the specific closure-hash algorithm (git-blob-hash concatenation); the discrimination control (§4 check 4) is an addition motivated by Law 13 and wsc's recorded history, not by Law 14's staleness clause specifically — Law 14 does not itself require a discrimination control, and this document adds one anyway because §4's own analysis shows staleness-checking alone would not have caught wsc's actual symptom |
| "recalibration is an explicit re-baseline... generation identity... consumers record the generation" | §12 (`CALIBRATION_GENERATION`) | the specific stamp-as-blob-hash mechanism; the review-weight question is left open (design-review question 4) |
| "coefficients cite, they do not copy... bound... by a mechanical check" | §6 (citation + `bindings`/codegen) | the `bindings` array shape; the codegen-preferred-over-comparison ordering (Law 13's own general preference, applied here) |
| "honesty in output: how many microarchitectures... validated on... model-internal... may not be cited as facts" | §10 (`CalibrationStatus`), §11 (`modelInternalUnvalidated`, discriminating-kernel promotion) | the specific `CalibrationStatus`/`CalibratedCost` Lean types; `syntheticBound` as a fourth category for `idealProfile` is this document's own addition — Law 14's text has no notion of a profile that is deliberately never measurable, only "validated" vs. not |
| "gate: `python scripts/check_calibration.py`, registered in §4.1 Pillar 1" | §13.2 below | the specific checks the gate runs (closure hash, profile-existence, bindings, controls, discrimination) are this document's design, not the law's text, which names only the gate's existence and location |

Two items in this document are **not** derived from Law 14 at all, and are named here so
that is not silently implied: **§9's Agner Fog/uops.info licensing determination** is
Law 4-derived (external reference ingestion), not Law 14; and **§1's CSV weaker-tier
escape hatch** is this document's own accommodation for a measurement shape (large
sweeps) Law 14's text does not distinguish from a scalar measurement.

### 13.2 Wiring the gate (the predecessor lesson: "never wired into the build")

Law 14's own text points at its gate ("registered in §4.1 Pillar 1"), but as of this
document's authoring, `docs/REVIEW.md` §4.1's Pillar-1 list does not yet carry that
registration — this document does not add it. Landing that one line is left to the
owner/coordinator to do centrally, since multiple agents currently edit `docs/REVIEW.md`
concurrently and a locally-authored registration risks an avoidable merge conflict.

**The consolidated gate runner is the component that must invoke `check_calibration.py`.**
This document specifies the acceptance evidence `scripts/run_gates.py` must produce for the calibration gate
specifically, mirroring the meta-gate-fixture convention this project already uses
elsewhere (T4/T2's planted-`sorry`, broken-REF, duplicate-heading fixtures): a
**planted-bad calibration file** (stale closure hash, undefined profile, missing
`controls` block, a `bindings` mismatch) that `check_calibration.py` must reject, and a
genuinely valid file it must accept, checked into a fixtures directory the gate runner
exercises on every invocation, not merely asserted to work once by whoever writes the
tool.

None of the above builds `check_calibration.py` itself — that remains implementation,
out of scope for this design stage, and is what F2's implementation follow-up and TC5
actually deliver.

## 14. What this deliberately does not solve (open, not silently dropped)

- **§4's accepted coarseness** (closure-hash invalidating on non-semantic edits) is not
  solved — a declaration-level/AST-aware hash would reduce false-positive churn but is
  real tooling investment not scoped here.
- **§7's residual** (a sufficiently determined forger could still fabricate a
  self-consistent raw-sample array) is accepted, not solved, and is explicitly not
  treated as this document's primary risk per the design-review disposition.
- **§11 is resolved, not open** — see §17: no PMU path, uop counts are model-internal
  parameters validated via discriminating-kernel cycle measurements.

## 15. What this does not foreclose

- F3's staged calibration can start writing files into `calibration/x86_64/` the moment
  `check_calibration.py` and the `check_refs.py` `DOC_DIRS` change exist.
- Future GPU/transport calibration work reuses the same schema under `calibration/transport/`,
  `calibration/storage/`, `calibration/network/` without a second design pass, modulo
  §1's CSV weaker-tier declaration where per-cell raw retention proves impractical.
- Nothing here mandates a specific reduction statistic beyond "median-of-N, not mean" —
  a harness for a different measurement class may name a different `reduction.method`
  as long as it is a pure, committed, re-derivable function §6 can bind against.

## 16. Disposition of the prior draft's design-review questions

The redesign review resolved five of the prior draft's six open questions explicitly
rather than leaving them open; recorded here so this section doesn't silently drop them:

1. **Host identity** — resolved: opaque `host_id` plus a `host_fingerprint` collision
   check (§2.1). Anonymity is fine; unverifiability is not.
2. **Tooling boundary** — resolved: `check_calibration.py` only. No second
   `regenerate`-style CLI; the tooling budget goes to wiring it into Pillar 1/TC5 (§13),
   not building a parallel mechanism.
3. **CSV-sweep raw-sample scale** — superseded: the question was one level too shallow;
   §1 now mandates per-cell raw retention directly, with an explicit weaker-tier escape
   hatch rather than leaving the scale question open.
4. **Sequencing the `check_refs.py` change** — resolved: land `DOC_DIRS` now, standalone
   (§1) — verified no-op while `calibration/` is empty.
5. **Multi-machine roadmap / profile deletion** — resolved: neither keep-silently nor
   delete; mechanize the marking (§10). The remedy for dead
   *fields*, not profiles — a different entry, not a precedent for removing
   `skylakeProfile`/`zen4Profile`.
6. **Residual hand-edit gap** — resolved: the named residual (forging a self-consistent
   raw array) was not the actual risk; the suggested mitigation (a CI check forcing a
   `harness_commit` bump on every diff) was itself harmful — it is exactly the escape
   hatch §4 now removes, since it trains hand-editing provenance fields as a normal,
   expected action.

## 17. Review history: rulings across three cycles

Recorded here for the same reason §16 records the first cycle's dispositions — so
nothing is silently dropped across repeated rounds of review:

1. **Cycle 2, §11 arbitration: no PMU path; reframed as model-internal parameters.**
   The first revision's framing ("RDTSC cannot measure uop counts," flagged for
   arbitration between scoping in a PMU path or accepting indirect-only validation)
   conceded too much and posed a false choice. The ruling: uop counts are not
   observables, they are internal model parameters; the observable is time, and RDTSC
   already measures that fine. F3 stage 1 is retitled "derive coefficient corrections
   from cycle measurements on discriminating kernel pairs," not "measure uop counts" —
   see §11 for the full mechanism (mutation-testing-shaped discriminating pairs, a
   `modelInternalUnvalidated` status tag, promotion to `siliconValidated` only on an
   actual discriminating measurement or a vendored source). No PMU, no signed driver, no
   new TCB entry, and no silent "stays invented" outcome.
2. **Cycle 2, Law 14 pulled back from `docs/REVIEW.md` to a proposal.** The first
   revision had added Law 14's text directly to `docs/REVIEW.md` alongside the Pillar-1
   gate registration. Ruling: only the Pillar-1 gate registration was sanctioned; a new
   numbered Law is the repository owner's governance surface to ratify, not an
   implementing agent's or a design doc's to assert into force. The second revision
   removed the Law-14 text from `docs/REVIEW.md` entirely, kept only the Pillar-1 item
   there, and moved the full proposed Law 14 text into this document, explicitly marked
   pending owner ratification.
3. **Cycle 3: the owner has ratified Law 14.** The coordinator wrote Law 14 into
   `docs/REVIEW.md` on the integration branch (with the README law summary and law-count
   references updated) and instructed that this document be rebased onto that commit,
   touch `docs/REVIEW.md` not at all (not even the Pillar-1 line, which the coordinator
   applies centrally), and be rewritten to **cite Law 14 as ratified law rather than
   propose it** — checking that every requirement here is either derived from Law 14's
   text or explicitly flagged as additional. This revision does that: §1 quotes the
   ratified text and closes the gap-between-laws argument as resolved rather than
   proposed; §13.1 is the new requirement-by-requirement traceability table the
   coordinator's instruction asked for; every remaining "proposed"/"pending
   ratification" framing from cycle 2 is removed. This document was rebased onto commit
   `340aa4f` (`docs(governance): Law 14 ratified; ADR corpus, task DAG, ledgers, frontier
   tooling`) so `docs/REVIEW.md` in this branch is byte-identical to the integration
   branch's ratified version — verified by `git diff` showing no difference.

## Design-review questions (this revision)

1. **Closure-hash granularity (§4)** — is byte-content hashing's false-positive churn
   (a comment edit invalidating every dependent calibration file) tolerable long-term,
   or does F3's stage-2/3/4 rewrite cadence make declaration-level/AST-aware hashing
   worth the tooling investment sooner than "someday"?
2. **`MicroarchProfile.clockProvenanceRef` ownership (§2.4)** — should this small
   Lean-side schema addition land as part of F2's implementation follow-up (so the field
   exists before F5 starts) or as F5's own first deliverable (since F5 is the only
   actual consumer)?
3. **Discrimination-pair scope (§4 check 4, §11)** — is one universal required-to-differ
   kernel pair sufficient for the x86-cycles domain, or does every measurement class
   (PCIe transfer, disk, network) — and now also every individual model-internal
   parameter §11 wants promoted out of `modelInternalUnvalidated` — need its own
   purpose-built discriminating pair, which could grow into a sizable curated suite
   rather than one or two fixed pairs?
4. **Generation re-baseline review weight (§12)** — should a `CALIBRATION_GENERATION`
   bump require a second-reviewer/approval step before merge (since it can silently
   move build-failing cost budgets across many routines in one commit), or is ordinary
   PR review sufficient given §12's requirement that the bump be its own legible commit?
