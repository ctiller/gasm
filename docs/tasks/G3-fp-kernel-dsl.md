---
id: G3
title: FP kernel DSL design (Deterministic Shader Profile)
status: ready
blocked_on: ""
after: [G1]
related: []
bar: ""
track: graphics
priority: 7.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G3: FP kernel DSL design (Deterministic Shader Profile)

## Context

`GRAPHICS_PREBUILD_AUDIT.md` §1 (Law 5 stop-and-design backlog) lists "Floating-point
determinism profile" as item 5 and calls it, verbatim, **"the hardest open question in the
plan."** Like G2, this task depends only on G1 landing — it is one of the two
per-`docs/adr/0011` "mandated designs rather than per-spike ad hoc reasoning" for the
graphics path, alongside G2's synchronization DSL. Neither doc currently says anything
about floating-point equivalence; the audit calls this "MAJOR, docs silent" (§2).

### The spec fact that forces this design

Audit §2 quotes the Vulkan specification directly: **"not pixel exact... does not
guarantee an exact match between images produced by different Vulkan implementations"**
(`appendix_i:24-26`). This is not a gap in `gasm`'s model that could be closed by more
careful proof engineering — it is the Vulkan specification itself declaring cross-driver
bit-exact equality out of scope. The audit elaborates: "repeatability is per-device only
and relaxed for shaders with side effects (i.e. storage-buffer compute); absent
decorations, contraction/reassociation are permitted." Storage-buffer compute — exactly
Spike 6's shape after G1's redefinition — is explicitly named as one of the cases where
even per-device repeatability is relaxed absent specific decorations.

### The corollary this task resolves for G1

`docs/GRAPHICS_ARCHITECTURE.md` §7 item 3 (pre-G1-rework) specifies Spike 6 as rendering
"a multi-color gradient / triangle" with rasterization. The audit draws the direct
corollary: **"the planned gradient-triangle spike is the worst possible first spike"**
(rasterization tie-breaks are implementation-defined per the invariance appendix) — "Spike
6 should be compute-only." G1 (already scoped, see `docs/tasks/G1-graphics-doc-rework.md`)
redefines Spike 6 as parametric compute for exactly this reason. This task's job is to
author the formal profile that makes that redefinition sound: without a Deterministic
Shader Profile, "compute-only" narrows the *rasterization* nondeterminism but says nothing
about whether the arithmetic inside a compute kernel is itself deterministic or
cross-driver-comparable — that is a separate, still-open question this task answers.

### The buildable answer, quoted exactly

Audit §2: "Buildable answer: a **Deterministic Shader Profile** (integers + basic FP ops
only, NoContraction, float-controls execution modes as hard device preconditions) inside
which both-ways byte equality survives; outside it, ULP-tolerance refinement + liveness,
and cross-driver equality abandoned." This is a two-tier design: a restricted sub-language
of shader kernels (integer ops, basic FP ops, `NoContraction` decoration mandatory, and
Vulkan's `float-controls` execution modes — e.g. rounding-mode/denorm-preservation modes —
declared as *hard preconditions* a device must advertise support for before a kernel in the
profile may target it) for which both-ways byte-equal equivalence is provable exactly as
every other `gasm` contract is; and an explicit escape hatch outside that profile where the
project drops to ULP-tolerance refinement plus liveness (per
`docs/EQUIVALENCE_PROOFS.md` §1.1's nondeterministic-spec pattern: refinement + progress,
not equality) and abandons cross-driver bit-exact equality altogether, honestly, rather
than claiming it.

### Second determinism condition — ties to G6

Audit §2's closing sentence: "Second determinism condition: dispatch determinism requires
**disjoint invocation writes** — a per-invocation capability obligation (Law 11 machinery
as the determinism proof)." Even inside the Deterministic Shader Profile, a kernel where
two invocations race to write the same output location is nondeterministic regardless of
FP semantics — this is a *memory-safety* precondition, not an arithmetic one, and it is the
concrete link between this task and G6's Law-11 GPU capability mapping
(`OpAccessChain`/`OpLoad`/`OpStore` bounds proofs against descriptor ranges). This task
should state the disjointness obligation as a precondition of its determinism theorem and
point at G6 for how that obligation is discharged in the capability model, rather than
re-deriving G6's machinery here.

### Why a DSL, not a per-shader proof (D11)

Per `docs/VISION.md` §4's DSL-as-proof-leverage principle and `docs/adr/0011` (read-only,
owned by another agent), the Deterministic Shader Profile is authored as a *language*: a
restricted grammar of kernel operations such that membership in the grammar is itself the
proof obligation, and the determinism/ULP theorems are proven once, in total, over that
grammar — "determinism and ULP-bound theorems are proven once per kernel-language
membership rather than once per shader" (ADR 0011). A shader author does not re-prove
determinism per kernel; they prove their kernel type-checks as a member of the profile, and
inherit the total theorem.

## Deliverables & acceptance criteria

- A design document defining the Deterministic Shader Profile grammar precisely: which
  SPIR-V/GLSL-level operations are admitted (integers, basic FP ops — addition,
  subtraction, multiplication, comparison; explicitly excluding fused multiply-add unless
  `NoContraction`-guarded, and excluding transcendentals given MODEL_DEBT/audit's note that
  GLSL.std.450 extended instructions are not yet ingested per Law 4), which decorations are
  mandatory (`NoContraction`), and which `float-controls` execution modes must be declared
  and checked as hard device preconditions before a kernel may be dispatched against a
  device.
- A total theorem, proven over the profile grammar (not per-kernel): membership in the
  profile implies both-ways byte-equal equivalence between `evalShader` (the pure Lean
  specification function) and the actual SPIR-V-encoded kernel's execution, under the
  stated device preconditions. State explicitly what is excluded: any kernel using an
  operation, decoration, or execution mode outside the profile is not covered by this
  theorem and must instead carry the ULP-tolerance-refinement-plus-liveness contract shape.
- The disjoint-invocation-writes precondition stated formally as a hypothesis of the
  determinism theorem, with an explicit pointer to G6 for its discharge mechanism (a
  forward reference is acceptable here since G6 is a sibling task; do not attempt to design
  G6's capability machinery inside this task).
- The ULP-tolerance-refinement contract shape for kernels outside the profile: define what
  "refinement" means precisely (per `docs/EQUIVALENCE_PROOFS.md` §1.1's nondeterministic
  spec pattern — every machine behavior must be spec-permitted within N ULPs, plus a
  liveness/progress obligation), so that this escape hatch is itself formally stated, not
  left as an unspecified fallback.
- Per Law 13(4): state the differential/control-vector evidence downstream implementation
  (G4's harness, G7's Spike 6) will need to produce against this design — specifically an
  **FP-divergence canary** (per G4/audit §3: "a vector that differs when float-controls are
  not honored") that exercises the profile boundary directly, proving the profile's
  preconditions are load-bearing and not vacuous.
- Law-5/Law-13 discipline: design doc authored, then routed through fresh-agent design
  review before `design_review` is marked approved and before any Lean cites it.

## Pointers

- `docs/GRAPHICS_ARCHITECTURE.md:135-139` (§7 item 3, pre-G1-rework Spike 6 spec with the
  gradient/triangle and rasterization — G1 is rewriting this; this task's profile is what
  makes the *compute-only* redefinition sound, not merely stylistically preferable).
- `GRAPHICS_PREBUILD_AUDIT.md` §1 item 5, §2 (FP-determinism paragraph in full), §9 ranked
  amendment #4 — read in full.
- `references/vulkan/appendix_i__invariance.md` (grep-verified present in `references/vulkan/`)
  — the Law 4 ground truth for the "not pixel exact" / per-device-repeatability claims; cite
  exact paragraph numbers from this file when authoring the design doc (the audit's
  `appendix_i:24-26` citation is a line reference into this vendored file).
- `docs/EQUIVALENCE_PROOFS.md` §1.1 — the nondeterministic-specification pattern
  (refinement + liveness) this task's outside-the-profile escape hatch must instantiate,
  rather than invent a third equivalence shape.
- `docs/VISION.md` §4 (DSL-as-proof-leverage, D11) and `docs/adr/0011` (read-only) — the
  precedent for treating the profile as a language with total theorems.
- MODEL_DEBT.md §B4 (no FPU/SSE/AVX state on the CPU side — for context; this task is about
  the GPU/SPIR-V shader side, but the audit's ingestion-status note that GLSL.std.450 is
  not yet vendored constrains what the profile can admit for transcendentals) and §D
  (graphics-forward debt, brief cross-reference).
- G6's file (`docs/tasks/G6-vulkan-host-model.md`) for the disjoint-invocation-writes /
  Law-11 capability discharge this task's determinism theorem depends on as a precondition.
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing); this design targets a future
  `Gasm/Targets/*` shader-kernel-DSL module, name TBD during authoring.

## Notes

- 2026-08-27: priority 7.5 — FP kernel DSL design (Deterministic Shader Profile) gates G5; owner-prioritized graphics track.

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.)_
