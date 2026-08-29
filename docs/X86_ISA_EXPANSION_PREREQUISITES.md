# x86-64 ISA Expansion: Prerequisites Assessment

**Status:** historical assessment snapshot at commit `1e39e7e` (2026-08-28), with selected
post-assessment corrections. “Today,” task IDs, counts, and blocker labels in the preserved analysis
refer to that snapshot and are not an active task board. Current authority/borrowing work is owned by
`docs/MEMORY_MODEL.md` M1/M4; current target and decoder status by `docs/TARGETS/X86_64.md`;
calibration by `docs/CALIBRATION_GOVERNANCE.md`; and live merge gates by `docs/CI.md`. Where an
explicit “Current status” paragraph below conflicts with the historical diagnosis, that paragraph
wins. Nothing in this document is itself implementation.

**The question**: the owner is considering a massive expansion of the x86-64 instruction set —
a deliberate, eyes-open departure from Law 5 / D7 / `docs/VISION.md` §3.3's spike-by-spike
discipline, which exists because the predecessor (`wsc`) died by building out ISA code before the
instruction model was right. What must be pinned down first, so that the expansion is not more
expensive to unwind than to redo?

---

## 1. Verdict

**Not ready today. Expanding now would repeat `wsc` — but not in the place the starting
hypothesis pointed.**

The owner's initial view was "something around the x86 round trip proofs, performance model debts
would be baseline here." Half confirmed, half redirected:

- **The roundtrip proof machinery is the *healthiest* part of the instruction pipeline.** It is
  kernel-checked (`decide`, Law 10 rung 2 — zero allowlist entries), per-family sharded,
  registry-enforced, and the enforcement was re-verified live for this assessment by mutation
  (§4.1). Its debts are *build-structure* (the monolithic decoder couples every instruction edit
  to a 39-module rebuild) and *coverage convention* (curated witness lists), not proof shape.
- **The performance model is a confirmed blocker, in a specific sense**: every one of the 88
  instruction forms carries invented, uncited latency/port/throughput coefficients inline
  (`docs/TECHNICAL_NOTES.md` §2), and there is no calibration harness, no governance mechanism
  (F2/Law 14 — gate not yet implemented), and no per-instruction obligation. A 10× expansion
  multiplies invented coefficients into a model the owner calls a superpower, with the holes
  invisible by construction.
- **The largest prerequisite is one the hypothesis did not name: the machine-state schema and the
  memory-operand contract.** `X86_64MachineState` has no XMM/YMM registers, no MXCSR, no x87, no
  fault model beyond `#DE`, no segment registers, and a total `memory : Address → Byte` with no
  permissions (`docs/TECHNICAL_NOTES.md` §2). Any expansion worth calling "massive" reaches SIMD and
  memory-operand forms — the exact surface the current state type cannot represent and Law 11's
  unbuilt capability contract (PA4: zero modules migrated) does not yet govern. Instructions
  written against today's state type and today's raw-memory-operand convention would be written
  against a model already known to be wrong for them. That is not *like* the `wsc` failure; it
  *is* the `wsc` failure, one abstraction level down from where the hypothesis looked.

A secondary but hard finding: **`main` was red during this assessment** (§7.1) — two
independently-green branches merged into a deterministic build failure, because a proof coupled
to an interpreter definition's internal shape (`simp only [runProgramWithLoops]`) broke when a
perf change restructured that definition. At current team throughput this is an incident; at
expansion throughput it is the steady state, unless merge gating and a stable proof-facing
interface land first.

With the prerequisites in §3 met, the expansion is a sound project. Without P1–P4, it re-runs
`wsc` with better paperwork.

---

## 2. Evidence base (measured, this machine, 2026-08-28)

| Quantity | Value | How obtained |
| :-- | :-- | :-- |
| Instruction forms (`instance : X86_64Instruction`) | 89 instances = 88 concrete forms + the `AnyX86_64Instruction` wrapper | grep over `Gasm/Targets/X86_64/Instructions/*.lean` |
| Instruction families | 25 (`Add` … `Syscall`) | directory listing |
| LOC, `Instructions/*.lean` | 4,197 (≈478 shared `Base.lean`; ≈42 LOC per form) | `wc -l` |
| LOC, `RoundtripGate/*.lean` | 956 (26 files) | `wc -l` |
| LOC, `Decoder.lean` (monolithic) | 774 | `wc -l` |
| Roundtrip cases in the registry | 1,612 (per `d3c2fc2`'s gate run) | commit record; consistent with shard lists |
| Full build | 495 jobs; warm no-op ≈ 4 s | `lake build`, timed |
| **Cost of editing one instruction file** | **39 modules rebuilt, 130 s wall** (one added declaration in `Instructions/Add.lean`, `lake build Gasm`, then reverted) | measured; concurrent-agent contention present, consistent with B1's contention caveat |
| Cascade composition | all 26 `RoundtripGate/*` shards + `Common` + aggregator + `Decoder` + `Registry` + `Assembler` + `Disassembler` + both linkers + `SemanticsFuzzer` + `Core.Verification` + umbrella | build log module list |
| Registry gate enforcement | **verified live**: adding an unregistered `X86_64Instruction` instance fails the build at `Registry.lean:117`, naming the offending type | mutation test, then reverted (§4.1) |
| One pointwise spike-equivalence module (`Spikes.Spike2Fibonacci.Linux.Equivalence`) | 156 s elaboration in isolation; 247 s under load, where it also died once with a non-deterministic crash before succeeding on retry | `lake build <module>`, timed twice |
| `scripts/gate_allowlist.txt` | 85 entries: 36 grandfathered / 48 axiom-only / 1 finite-forall | parsed by category |
| Oracle debt added by the Linux target (one day, five spikes) | **+24 entries: 9 grandfathered pointwise `native_decide` + 15 axiom-only** | allowlist lines 152–175, diff of `a6a6381` |
| Oracle debt added by a new *instruction* (`SyscallOp`, same merge) | **0 entries** — its roundtrip shard is plain `decide` | allowlist diff |
| Forms with `canFuzzHardware := false` (zero silicon validation of semantics) | 50 of 88 (57%) | grep, type-level only; instance-level RSP filtering excludes more cases |
| Forms covered by the NASM encoding oracle | ≈21 of 88 (24%) — a hand-maintained 22-way `match` in `EncodingFuzzer.lean:78-115`, **not** derived from the registry | read directly |
| Forms whose uop/latency coefficients cite any calibrated or vendored source | 0 of 88 | `docs/TECHNICAL_NOTES.md` §2; spot-confirmed in `Add.lean` (`latencyCycles := 1, reciprocalThroughput := 0.25`, inline literals) |
| Dead perf fields still carried by every instance | `reciprocalThroughput` has zero read sites (with 4 more dead `MicroarchProfile` fields per A3) | grep re-confirmed |
| `partial def` in the x86-64/Linux/BareMetal instruction path | none — fuel recursion throughout | grep |

---

## 3. The prerequisites, ranked by cost of getting them wrong

Blocking = starting the expansion before this exists makes the expansion's own output wrong or
unusably expensive, and retrofitting costs more than waiting. Desirable = makes the expansion
cheaper or safer but does not invalidate its output.

### P1 — BLOCKING: settle the machine-state schema for the classes the expansion will cover

**Exists today?** No. `X86_64MachineState` (`Gasm/Targets/X86_64/Registers.lean`) is 16 GPRs +
RFLAGS + `rip` + a total `memory : Address → Byte` + a `faulted` bit. No XMM/YMM/ZMM, no MXCSR,
no x87, no segment bases, no fault taxonomy beyond `#DE` (`docs/TECHNICAL_NOTES.md` §2). The
hardware harness's 136-byte result record captures GPRs+RFLAGS only.

**Why it is the top item.** Every instruction's `step` function, every step lemma, every
equivalence proof, and the harness capture format are written against this type. If SIMD (or
even flags-model refinement) is added *after* hundreds of instructions land, every one of them —
and every proof over them — is touched again. This is structurally identical to the `wsc`
failure the owner described: "we didn't get the instruction model right and built out too much of
the isa as code." The current model is not neutral about SIMD; it is *wrong* for it, and
`PCLMULQDQ`/`MOVDQU`-class instructions are explicitly on the zlib epic's demand list
(`docs/ROADMAP.md`'s codec/performance direction).

**What "done" means.** A ratified design (Law 5, D18-gated — this is unambiguously a >10 kLOC
umbrella) covering: the extended register file and how existing GPR code migrates (ideally
without touching the 88 existing `step` functions — e.g. an extension-by-composition shape rather
than field surgery); MXCSR and the FP-semantics question (which interacts with the graphics
  track's determinism problem, `docs/GRAPHICS_ARCHITECTURE.md`); the fault taxonomy the expansion's
classes need; and the harness record extension for XMM capture. The design must state which
instruction classes it deliberately does **not** cover, so the expansion's scope can be cut to
match the model rather than the model silently lagging the expansion.

**Cost of getting it wrong**: the entire expansion is written against the wrong state type —
full `wsc` replay. This is the single highest-stakes item.

### P2 — BLOCKING: the memory-operand contract (Law 11 / PA4), at least at the instruction layer

**Current status:** the descriptor/frame layer exists, but the checked capability-authoring path
does not. `docs/MEMORY_MODEL.md` M1/M4 now owns the indexed provenance, typed-view, authority, and
cross-thread transition design that replaced the retired PA2/PA4 task labels. The owner's directive
remains explicit: instructions must validate access authority and fail to assemble when its proof is
absent.

**Why blocking.** A massive expansion is mostly *memory-operand* forms — that is where the
current ISA is thinnest and where real workloads live. Every memory-touching instruction
authored on today's bypass path (raw symbolic operands, no capability) is authored against the
wrong contract and must be rewritten when PA4 lands — the precise class of rework D7 exists to
prevent. Law 11's own text already prohibits new programs on the bypass path; an expansion that
adds hundreds of memory forms on it would be a law violation at scale.

**What "done" means.** Not full migration of `Stdlib/Zlib/Windows.lean` — that can lag. What
must exist *before* memory-form instructions are mass-authored is the **instruction-level
obligation shape**: how a memory-operand instruction structure carries its capability parameter,
what the assembler checks, and what the failing-to-assemble path looks like, reviewed and exercised
on at least one real instruction family end-to-end. **Status:** this is the M1/M4 exit path in
`docs/MEMORY_MODEL.md`; it is not implemented.

**Cost of getting it wrong**: every memory-form instruction written twice; the second writing
also invalidates any proofs written against the first.

### P3 — BLOCKING: B3 decoder modularization + the registry's import-closure hole

**Current status (updated 2026-08-28):** the Stage B decoder modularization described in
`docs/TARGETS/X86_64.md` §5 has landed. That section owns the measured build-shape result and
remaining explicit-CI caveat; the retired task record is no longer a coordination surface.

**Historical measured problem (before Stage B landed).** Adding one declaration to
`Instructions/Add.lean` rebuilt **39 modules in 130 s** in the assessment snapshot because
`Decoder.lean` (then a 774-line monolithic opcode chain) imported
every instruction file, and all 26 `RoundtripGate/*` shards import the decoder through
`Common.lean`. The cascade is proportional to **total ISA size, not to the change**. At 10×
(≈250 families, a ~7,000-line decoder, ~260 shards) the per-edit cascade projects to hundreds of
modules and tens of minutes — and per `docs/VISION.md` §4, agent iteration speed *is* checker
feedback latency, so this kills the expansion's own workforce. Two aggravators are already live
at 88 forms: intermittent `std::bad_alloc` under concurrent `decide` shards (documented in
`docs/TARGETS/X86_64.md` §3, and a non-deterministic single-module build crash was observed
during this assessment), and two shards already needing `maxRecDepth 4000`.

**What "done" means.** B3 as designed and amended by its B1-review note: per-family `tryDecode`
co-located with `encode`; each family's gate shard verifying against **its own** `tryDecode`;
dispatch exhaustiveness isolated into the one module allowed full fan-in; measured evidence that
editing one family rebuilds only that file + dispatcher + one lemma. Plus the ~10-line
filesystem-vs-import-closure check B3's notes demand: today a brand-new `Instructions/Foo.lean`
that is never added to the umbrella import is **invisible to the registry audit**
(self-documented at `Gasm/Targets/X86_64/Registry.lean:22-31`, still unfixed) — at 40
instructions that is an unlikely mistake; at 400, with many agents adding files concurrently, it
is a certainty. A parallelism cap or batching for the `decide` shards belongs in the same
change (the OOM class is aggregate memory pressure, and shard count grows linearly with
families).

**Cost of getting it wrong**: not correctness — throughput. Retrofitting B3 under 250 families
means restructuring a 7,000-line decoder instead of a 774-line one, with every family's gate in
flight.

### P4 — BLOCKING: make per-instruction validation obligations mandatory and *visible*

**Current status (post-assessment): substantially landed.** `roundtripCases`,
`validationOracle`, and `costProvenance` are mandatory instruction fields. The NASM encoding and
hardware-semantics suites are derived from `Registry.allEncodableInstructions`, and
`lake exe check_x86_obligations` checks non-vacuous uops/fuzz vectors, oracle consistency,
justifications, and explicit opt-outs against `scripts/x86_obligation_allowlist.txt`. The original
mutation finding below remains useful provenance for why those gates exist.

**Remaining gap:** hardware coverage is still limited for memory, control-flow, privileged, and
future SIMD forms, and all current cost coefficients remain explicitly uncalibrated. Expansion work
must extend the harness or carry counted, justified oracle debt; it may not revive a hand-maintained
generator or silent `canFuzzHardware := false` convention.

**Cost of getting it wrong**: hundreds of instructions whose semantics nothing ever checked,
with no ledger even recording which ones. `VISION.md` §3.3: "A complete, unvalidated model is a
liability."

### P5 — BLOCKING for the perf model's integrity: calibration governance before mass coefficient entry (F2 → F1; A3 cleanup)

**Current status (post-assessment): partial.** The RDTSC/RDTSCP measurement implementation now
exists in `Gasm/Targets/X86_64/HardwareTimingHarness.lean` with its contract in
`docs/RDTSC_HARNESS.md`. `costProvenance` is mandatory and `check_x86_obligations` reports every
uncalibrated coefficient. The remaining blocker is the governed calibration artifact/binding and
staleness gate described by `docs/CALIBRATION_GOVERNANCE.md`; `scripts/check_calibration.py` still
does not exist, and current instruction coefficients remain explicitly model-internal/unvalidated.

**Why blocking rather than desirable.** The owner has defined the perf model as the strategic
asset, and its failure mode under expansion is uniquely quiet: an instruction *cannot* land
without a `toUops` value (the field is mandatory), so every new instruction **will** get a
number — the only question is whether that number means anything. 10× instructions at the
current convention = hundreds of additional invented coefficients that are syntactically
indistinguishable from measured ones. The holes develop exactly where the new instructions are,
and are invisible — the owner's own framing of the risk, confirmed by the tree.

**What "done" means.** Not full calibration of every existing form, which can proceed in parallel
with early expansion waves. The remaining floor is: (i) a governed place for calibration data, a
citation convention, and staleness/hand-edit gates wired into `scripts/run_gates.py`; (ii) the live
harness measures each demanded instruction under the recorded profile; and (iii) every new
coefficient either binds to a calibration artifact or remains mechanically marked and counted as
model-internal. Also, before 10× copies are stamped out: delete or wire the dead
fields (`reciprocalThroughput` on `X86_64Uop`, the four dead `MicroarchProfile` fields —
`docs/TECHNICAL_NOTES.md` §2), since every dead field replicated into 800 instances is Law 8 debt that
gets 10× harder to remove. **Status:** harness and loud marking exist; governed binding/staleness and
broad calibration remain open in the named calibration documents.

**Cost of getting it wrong**: the "superpower" becomes a plausible-looking fiction precisely
over the new surface, and mis-ranks the optimization search (`VISION.md` §5's "actively
misleading" case). Recalibrating later is cheap per-coefficient but the *trust* damage is the
D24 lesson: a number that is plausibly wrong is worse than one that is obviously missing.

### P6 — BLOCKING as a process gate: merges verified in the merged tree, mechanically

**Exists today?** No — demonstrated by counterexample during this assessment (§7.1): `main` at
`1e39e7e` fails `lake build` deterministically. Two branches, each green in isolation, merged
red; D6's rule ("agents' claimed results are unverified until re-run in the merged tree")
exists on paper and was not mechanically enforced. CI exists (GitHub Actions, `docs/CI.md`) but
did not block the historical merge; the consolidated runner is now documented in `docs/CI.md`, but
nothing forces it between merge and push.

**What "done" means.** A merge cannot reach `main` without a full-mode gate run of the *merged*
tree exiting 0 — branch protection on the GitHub side or an enforced local merge-train script;
either way mechanical, not conventional (Law 13). At expansion throughput — dozens of agents
landing instruction families concurrently — the two-green-branches-one-red-merge interaction
rate grows quadratically with in-flight branches; this is the single cheapest prerequisite and
the one with the steepest scaling payoff. **Status:** the runner exists; repository/branch
enforcement is an external configuration concern recorded by `docs/CI.md`, not a retired task ID.

### P7 — DESIRABLE (strongly): a stable proof-facing interface before mass proof authoring (PA2)

The incident in §7.1 happened because a proof used `simp only [runProgramWithLoops]` —
definitional unfolding of the interpreter — and the interpreter's internals changed shape
(B4's indexed lookup). PA15's own loop-invariant work created the first reusable unfolding
lemmas (`runProgramWithLoops_step`/`_stuck`), which is the right instinct, but they too are
proved *by* definitional simp and broke with it. The stable step-lemma/composition API historically
labelled PA2 is the fix: proofs consume a lemma API, and interpreter
restructurings re-prove a handful of lemmas instead of breaking every downstream proof. The
expansion's per-instruction step lemmas should be authored against the stable shapes, which argues
for their design (not full implementation) preceding the expansion's convention freeze.
Desirable rather than blocking because the expansion's first waves could restrict themselves to
encode/decode/uops/fuzz surface and defer step-lemma authoring — but if per-instruction lemmas
are in the expansion's definition of done (they should be), that API design becomes blocking for
that part. Current ownership is `docs/SOFTWARE_MODELING_SDLC.md` plus the relevant subsystem stage,
including `docs/MEMORY_MODEL.md` M0/M1 for memory-facing proofs.

### P8 — DESIRABLE: registry-scale hygiene items

Each cheap, none individually blocking, all 10× harder after the expansion:

- **`decodesOk`'s misdecode guard compares `toLean` strings** (`RoundtripGate/Common.lean:37-44`)
  because `AnyX86_64Instruction` erases `DecidableEq`. At 88 forms, distinct-forms-rendering-
  identically is implausible; at 880 it is merely unlikely, and a collision would silently
  weaken clause (d) of the gate. Add a registry-level check that `toLean` is injective over
  `allEncodableInstructions` (decidable, cheap, fits the existing `run_cmd` audit), or give the
  wrapper a tag-based equality. **Status**: proposed here; does not exist.
- **`expectedInstructionTypes` is a hand-maintained `List Name`** — mechanically checked against
  the live environment (verified, §4.1), so it cannot *drift*, but at ~800 entries it becomes a
  merge-conflict magnet with every concurrent instruction branch touching the same list. B3's
  registry-driven dispatch should consider deriving it per-family (each family file owns its
  manifest slice) for conflict-freedom.
- **Naming conventions** (`AddR64Imm8` / `add_r64_imm8` / `"add_r64_imm8 ..."` toLean strings)
  are consistent but nowhere specified. Write the one-page convention (operand-order, width
  suffixes, SIMD register naming) into `docs/TARGETS/X86_64.md` before 30 agents each invent a
  dialect. **Status**: convention doc section does not exist.
- **Provability-forfeiting choices to ban in the expansion's conventions**, generalizing the
  `partial def` lesson (four confirmations today; the x86 path is currently clean —
  grep-verified zero `partial` in the instruction/semantics path): `partial def` and `mutual
  partial` (kernel-opaque, zero equations — the Wasm interpreter's allowlist entry documents the
  cost); well-founded recursion where equation lemmas get stuck under kernel `decide`
  (the LEB128 case); `Inhabited`-instance fabricators on oracle result types (TCB T10);
  `.getD`/fallback defaults on lookup paths (the assembler's silent jump-to-self, hardened only
  in `d3c2fc2`); string-equality standing in for structural equality (the `toLean` item above);
  and definitional `simp` against interpreter internals (P7). Each is cheap to forbid in a
  convention document and expensive to excavate from 40 kLOC.

### P9 — DESIRABLE: keep the oracle-debt convention from multiplying through the expansion's validation vehicles

The measured data is unambiguous about *where* allowlist debt comes from: the `SyscallOp`
instruction added **zero** entries (its gate is `decide`), while the Linux *target* added **24**
in one day (9 grandfathered pointwise `native_decide` trace-equivalence proofs + 15 axiom-only
downstream — allowlist lines 152–175). Instructions are debt-neutral under the current gate
design; **spike×target pointwise equivalence proofs are the debt mint**, at ~5 entries and
(measured) ~150 s of `native_decide` elaboration per spike×target module. The expansion itself
therefore does not need the PA6/PA7/PA8 chain as a prerequisite — but its *validation vehicles*
do: if each instruction wave is exercised by new spike-shaped programs proved pointwise, the
ledger grows by the convention, not the ISA. The expansion's definition of validation should be
registry-derived differential fuzzing (which is allowlist-free) plus PA2-style structural
step lemmas — not new `*_trace_equivalence : ... := by native_decide` theorems. D29 already
frames the trajectory correctly (reduce, demonstrate, then ratchet); the expansion just must not
be the thing that reverses the trend.

---

## 4. The seven questioned areas, answered against the tree

### 4.1 Roundtrip proof shape (question 1)

**How it works today** (read + verified): every instruction form's typeclass instance must
supply `roundtripCases` (no default — omission is a compile error). 26 per-family shards each
prove `<family>Cases.all decodesOk = true` **by plain `decide`** — kernel-checked, no axiom, no
allowlist entry; two shards need `maxRecDepth 4000`, still `decide`. `Registry.lean`'s
`run_cmd` audit walks the *live environment's* instance table and diffs it against the manifest.
**Mutation-verified for this assessment**: a probe `instance : X86_64Instruction
MutationProbeInstr` with no manifest entry failed the build at `Registry.lean:117` naming the
probe type exactly. So: not monolithic (per-family shards), not `native_decide` (all `decide`),
and genuinely omission-proof for any instance the import graph can see.

**The honest caveats**: (i) the proof is exhaustive over *curated witness lists*, not operand
domains — `docs/TARGETS/X86_64.md` §1 documents the convention and its known holes (the
both-extended-REX gap was exploited by a reviewer mutation before being patched with exactly
three witness pairs); a universal per-family `∀ operands, decode (encode i) = i` is the B3-era
upgrade path once decode is co-located. (ii) One structural hole: an instruction *file* never
imported into the umbrella is invisible to the audit (`Registry.lean:22-31`, self-documented;
the ~10-line closure check is designed in B3's notes, unbuilt). (iii) At 10×: `decide` time
scales linearly and is fine per shard; the binding constraints are concurrent-shard memory
(already intermittently OOMing at 26 shards) and the 39-module/130 s edit cascade — see P3.

### 4.2 Semantics validation for a new instruction (question 2)

Mandatory: encode/decode roundtrip (above). Automatic-but-escapable: hardware semantics fuzzing
— the suite is derived (`allEncodableInstructions.filter canFuzzHardware`), so a new instruction
is fuzzed *unless* it sets `canFuzzHardware := false` or generates few/no states, and nothing
audits the opt-out (50/88 forms opted out today; the mutation probe with zero fuzz states
compiled cleanly). Convention-only: NASM encoding oracle (hand-list, ≈21/88 forms). Absent:
any perf-coefficient obligation. So yes — **it is possible today to add an instruction whose
semantics and cost nothing checks**, provided its bytes roundtrip. P4/P5 are the closures.

### 4.3 Oracle debt per instruction (question 3)

Measured: **0 allowlist entries per instruction; ~24 per target (9 grandfathered + 15
axiom-only across 5 spikes); ~5 per spike×target.** Current ledger: 85 entries (36/48/1). The
brief's "eight new grandfathered" undercounted by one — the Linux block contains 9. The
convention change that makes expansion debt-neutral is not about instructions at all (they
already are neutral); it is P9 — validation vehicles that do not mint pointwise
trace-equivalence theorems.

### 4.4 Performance model (question 4)

Confirmed blocker; see P5. The one structural positive: `toUops` is a mandatory field, so the
hook where a cost-model obligation would attach already exists on every instruction — what is
missing is any check that its value is calibrated, cited, or even non-empty.

### 4.5 The `partial def` lesson (question 5)

The x86-64 path is clean (grep-verified: zero `partial` in the instruction/semantics path; fuel
recursion throughout, which is why its proofs close). The generalized list of
provability-forfeiting choices the expansion's conventions must ban is in P8, drawn from
incidents already recorded in this tree.

### 4.6 Memory capability, Law 11 (question 6)

Zero modules migrated (Law 11's own Status line); PA4 `ready` but design-gated behind PA2 and a
D18 scoping conversation that has not happened. Blocking for memory-form instructions — P2.

### 4.7 Build time (question 7)

Measured figures in §2; projection and fix in P3. Headline: **per-instruction-edit cost is
39 modules / 130 s at 88 forms and scales with total ISA size**; the fix (B3) is fully designed
and unimplemented. The build is 495 jobs (not the ~428 in the brief — the Linux target grew it);
warm no-op ≈4 s; a single pointwise spike-equivalence module costs ~156 s of `native_decide`
elaboration, which is a per-target cost, not per-instruction.

---

## 5. What the hypothesis got right and wrong

**Right**: the perf-model debt is baseline-level — P5 confirms it, with sharper mechanics than
"debts": the danger is specifically that mandatory-but-unchecked `toUops` fields guarantee
plausible fake numbers at scale. **Redirected**: the roundtrip proofs are the *strong* link;
their real exposure is build topology (P3) and witness-coverage convention, not proof shape.
**Missed** (the two most expensive items): the machine-state schema (P1) and the memory-operand
contract (P2) — the instruction *model* itself, which is where `wsc` actually died; and the
merge/proof-coupling fragility (P6/P7), which this assessment watched happen live.

---

## 6. Recommended shape of the expansion, when its prerequisites are met

**Status**: proposal only; nothing below is designed or scheduled.

Not one bulk import — waves by model-readiness, each wave differentially validated in the change
that lands it (keeping D7's *validation* half even while relaxing its *demand-driven* half):

1. **Wave A — GPR-only ALU/flags forms** (missing Jcc condition families, r8/r16/r32 widths,
   ADC/SBB/BT*, MOVSX/MOVZX widths, etc.): representable in today's state type; safe after
   P3+P4+P6, with P5's marking convention so their coefficients land honest.
2. **Wave B — memory-operand forms**: after P2's instruction-level capability shape and the
   harness's scratch-region support, so their semantics are actually
   fuzzable on silicon and their contracts are the final ones.
3. **Wave C — branches/calls variants**: after harness landing-pad support (same Phase 3 item).
4. **Wave D — SIMD/FP**: only after P1's schema lands; this wave is where the expansion earns
   its keep for the zlib epic, and it is the one that must not be attempted on today's model.

Each wave's definition of done: registry-gated roundtrip (already forced), silicon fuzz or
ledgered opt-out (P4), NASM coverage via the derived generator (P4a), coefficient
citation-or-marking (P5), step lemma per PA2's shapes (P7), and REF citations into
`references.json`'s `intel-sdm` entry (already the working convention; note its pinned PDF is
the -078US/Dec-2022 edition — adequate for these waves' instructions, but `instr=`-anchor
resolution should be spot-verified for any post-2022 extension before Wave D grows into AVX-512
territory).

---

## 7. Findings nobody asked for

### 7.1 `main` was red during this assessment (cross-merge proof breakage, live specimen)

At `1e39e7e` ("merge: test-suite perf — concurrent gate scans and indexed simulator"),
`lake build` fails deterministically: `Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean:362,376`
— unsolved goals. Mechanism, verified from the git graph: PA15's loop-invariant proofs
(`cc8809b`, merged `7890c8d`) unfold `runProgramWithLoops` definitionally via `simp only`; the
B4 indexed-simulator change (`170f3e4`, merged `1e39e7e`) restructured that definition into
`runProgramWithLoops.loop (indexInstructions …)`. Each branch was green in isolation —
`170f3e4`'s commit message truthfully reports "lake build succeeds (424 jobs)" *for its own
branch, which predated PA15's file*. The merged tree was never rebuilt before landing. Three
prerequisites in one incident: P6 (mechanical merge gating), P7 (proofs must consume a lemma
API, not interpreter internals), and a calibration point for review capacity at expansion
throughput. Also observed during the same session: one non-deterministic single-module build
crash (the known concurrent-`decide`/elaboration memory-pressure class), which passed on retry —
the P3 aggravator.

### 7.2 The encoding oracle missed the registry retrofit

When TC4 derived the semantics-fuzzer suite from the registry, the NASM encoding fuzzer's
generator was left as a 22-way hand `match` (≈24% form coverage). Same defect class the registry
was built to kill, one file over. Cheap fix, listed in P4(a). **Status**: unfixed; no task ID.

### 7.3 The allowlist's mojibake

Multiple `scripts/gate_allowlist.txt` justification fields contain double-encoded UTF-8
(`Ã‚Â§`, `ÃƒÆ'Ã‚Â¢…` for `§` and `∀`) — harmless to the parsers (justification is free text) but
evidence that some tool in the pipeline wrote the file under the wrong codepage; worth fixing
before the ledger becomes the public face of the debt count. **Status**: unfixed; no task ID.

### 7.4 Retired task-board status vs reality

The retired board still showed PA1/TC5/B4 and others unchecked while the historical oracle-debt
audit and the git log showed them landed (six stale statuses were corrected; B4 landed in
`170f3e4` yesterday against a task file still `ready`). Known gap (TC13 unbuilt), but at
expansion concurrency a hand-synced board is not a coordination surface — TC13's regenerator
graduates from convenience to prerequisite-adjacent.

### 7.5 `docs/TARGETS/X86_64.md` §3 still displays a theorem about symbols that do not exist

`x86_mov_store_is_release` references `m.getMemoryType` / `m.isNonTemporalInstr`; neither
exists anywhere in the tree (the historical model-debt audit flagged this; still true). It survives the
doc-facade linter (a display-quoted theorem, not a MUST-claim), but an expansion team reading
the target spec as ground truth would be misled about the memory model's actual state. Fix is a
one-paragraph honesty edit — do it before onboarding an expansion team onto that document.

**RESOLVED 2026-08-28**: the theorem block is removed; `docs/TARGETS/X86_64.md` §3 now carries
an explicit `**Status**:` marker separating hardware ground truth (real) from model claims
(none). The cross-architecture design is `docs/MEMORY_MODEL.md`; its x86 realization is
stage M2-X and Spike 8 is the validation vehicle. Any wave containing a `LOCK`-prefixed RMW,
`CMPXCHG`/`XADD`, a memory-operand `XCHG`, or a fence therefore depends on M0 plus M2-X, so
atomicity and ordering semantics land with the first such form rather than after it. The linter blind spot this finding exposed — a
fenced ` ```lean ` code block declaring a theorem whose name exists nowhere in the tree is
structurally invisible to `MECHANISM_ABSENT`'s same-line prose shape, and a fabricated
theorem is *more* misleading than fabricated prose — is now covered by
`scripts/check_doc_facade.py`'s `THEOREM_FENCE_ABSENT` check.

---

## 8. Summary table

| # | Prerequisite | Exists? | Blocking? | Tracking |
| :-- | :-- | :-- | :-- | :-- |
| P1 | Machine-state schema for expansion classes (XMM/MXCSR/faults) | No | **Yes — highest stakes** | `docs/TECHNICAL_NOTES.md` §2; design decision required |
| P2 | Memory-operand capability contract at instruction layer | No (zero migrated) | **Yes** for memory forms | `docs/MEMORY_MODEL.md` M1/M4 |
| P3 | Decoder modularization + import-closure check + shard-parallelism cap | Yes, with explicit-CI caveat | previously blocking | `docs/TARGETS/X86_64.md` §5 |
| P4 | Mandatory, visible per-instruction validation (registry-derived encoding, opt-out ledger, status table) | Yes, with hardware-coverage debt | Maintain as a gate | `check_x86_obligations`; registry-derived fuzzers |
| P5 | Calibration governance + RDTSC harness + coefficient marking; delete dead uop fields | Partial: harness/marking exist, governed binding does not | **Yes** for perf-model integrity | `docs/RDTSC_HARNESS.md`; `docs/CALIBRATION_GOVERNANCE.md` |
| P6 | Merge gating on merged-tree full build | Runner exists; external enforcement must be checked | **Yes** — cheapest item | `docs/CI.md` |
| P7 | Stable proof-facing lemma API before step-lemma authoring | No | Desirable→blocking for lemma deliverables | `docs/SOFTWARE_MODELING_SDLC.md`; owning subsystem stage |
| P8 | Registry-scale hygiene (toLean injectivity, manifest sharding, naming doc, forfeit-list) | No | Desirable | unfiled |
| P9 | Expansion validation vehicles that mint no pointwise oracle debt | Convention risk | Desirable (policy) | `docs/EQUIVALENCE_PROOFS.md`; `docs/REVIEW.md` oracle gates |
