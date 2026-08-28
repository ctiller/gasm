# Direction review of `docs/TRUST_PLAN.md`

**Status**: this is a review artifact. It is not a specification, and it reports no machinery this
pass built. Every mechanism it names as absent is marked absent, and every change it proposes is a
proposal awaiting the owner's ruling. No file other than this one was changed. Where it displays a
theorem name, that name is quoted from a `.lean` file in the tree and its location is given.

This review does not re-run `docs/TRUST_PLAN_REVIEW.md`. That pass asked whether the plan was
factually correct and correctly sequenced, found six false claims, and they were corrected. Its
confirmed findings are inherited. This pass asks the different and larger question: **is the
direction right at all?**

## Measurement pin

Two tips disagree, and the difference matters to every count below.

| | commit | entries | `grandfathered` | `axiom-only` |
|---|---|---:|---:|---:|
| `origin/main` | `9a178de` | 78 | 34 | 44 |
| local `main` (20 commits ahead, unpushed) | `d313251` | **73** | **29** | 44 |

The five-entry difference is unpushed work that landed during this review and is itself evidence
(§2.2). Counts below are stated against local `main` unless marked otherwise. The working tree is
additionally dirty with several agents' in-flight edits; I read committed state except where noted.

---

## Verdict

**Spike-by-spike is the wrong shape.** But the brief's proposed alternative — one trace-equivalence
theorem covering many spikes — is also wrong, and for the reason the brief anticipates: the spikes'
obstructions genuinely differ. The right structural change is one level lower and already designed,
already partly built, and already demonstrated once in this tree. §3.

**A larger finding sits above that question and reframes it.** The plan's goal —
`scripts/gate_allowlist.txt` at zero — is a proxy that can be driven to zero without fixing the
defect ADR-0038 names. It is not merely a weak proxy; **the sanctioned way to retire an entry is to
make the pointwise check invisible to the only mechanism that tracks pointwise checks.** This has
already happened, twice, and one instance is in the last five retirements. §2.

This is the same class of finding as `docs/CITATION_REVIEW.md` and `docs/DOC_JUSTIFICATION.md`: a
mechanism the project relies on is producing the opposite of its intent.

Answers to the five secondary questions: the target should not be a count of allowlist entries at
all (§5); hedging survives in E, F and G, and the plan as a whole has the hedge's shape (§6); the 78
are not covered and the plan cannot tell whether they are (§7); the propagation claim is false as
stated, and I found the counterexample class (§8); a prevention exists, is cheap, and is legitimate
under ADR-0038 in the order that ADR prescribes (§9).

---

## 1. What the convention actually is, measured

`scripts/gate_allowlist.txt`'s `grandfathered` entries are not one convention. They are **two
schemas**, and the plan treats them as one population.

**Schema I — whole-program trace equivalence at one environment (21 of 29).** Every spike's
`Equivalence.lean` instantiates a whole-program contract and fills its trace-equivalence field. The
contract is universally quantified in its type; the quantifier is instantiated at a type that is not
the program's input domain. Measured across the tree — 18 instantiations:

| `Env` type | count | files |
|---|---:|---|
| `Unit` | 7 | Spike 1 ×4, Spike 2 ×3 |
| `Bool` | 2 | Spike 3 Windows, Spike 3 Linux |
| `Spike3SampleEnv` | 1 | Spike 3 Wasm |
| `HttpRoute` | 3 | Spike 4 ×3 |
| `GzipOp` | 3 | Spike 5 ×3 |
| `GunzipOp` | 2 | Spike 5 gunzip ×2 |

**Zero of the 18 bind a byte-array input domain.** `Spikes/Spike3SortLines/Windows/Equivalence.lean`
says so itself, at length, in the PA17 domain-honesty note above its `EnvironmentLoader Bool`
instance: `Bool` is "a two-element proxy standing in for exactly the two literal vectors above".

**Schema II — codec roundtrip at one or two literal vectors (8 of 29).** No machine trace, no
target, no environment: a `ByteArray` literal through compress-then-decompress.
`Stdlib/Zlib/Equivalence.lean` ×4, `Stdlib/Png/Equivalence.lean` ×2, `Spikes/Spike5Gzip/Equivalence.lean` ×2.

These two schemas have nothing in common except the tactic. They need different work, retire on
different paths, and — critically — have **different propagation behaviour** (§8). `docs/ORACLE_DEBT.md`
Part 1 drew exactly this distinction on 2026-08-27 and named it "shapes, not a flat list". The plan
does not cite that document and does not use the distinction. §4.

---

## 2. The central finding: the score can reach zero without fixing the defect

### 2.1 The mechanism

`scripts/check_gates.py` gates three tactic spellings: `native_decide`, `decide` reaching a
`+native` / `(native := true)` flag, and `bv_decide` (`NATIVE_DECIDE_REGEX`, `DECIDE_NATIVE_REGEX`,
`BV_DECIDE_REGEX`, at `scripts/check_gates.py:183-199`). `Tools/CheckGatesAxioms.lean`, the
load-bearing gate, keys on kernel-recorded axiom dependencies.

A plain `decide` or `decide +kernel` introduces no axiom. `docs/REVIEW.md` Law 10 states this
explicitly at rung 2: "a `decide` occurrence needs no `scripts/gate_allowlist.txt` entry at all".

Therefore **converting a pointwise `native_decide` to a pointwise `decide` deletes its allowlist
entry, and the stale-entry check makes deleting it mandatory.** The proposition does not change. The
domain does not change. The pointwise defect does not change. The score moves.

`scripts/check_gates.py`'s own docstring states the real rule — "Single-ground-instance checks are
regression tests, not verification" — and records that an earlier auto-pass shortcut "let new,
unreviewed pointwise checks slip in silently; it has been removed". The rule is written down. The
mechanism enforces it only for declarations that happen to carry an axiom.

### 2.2 It has already happened, and the last five retirements contain both kinds

Local `main` moved 78 → 73 during this review, in one commit, `f2b4bf3`. Its message reports the
move as a single number. It is two different things:

- **Four genuine harvests.** `deflate_roundtrip_{empty,soundness,repetitive}_inst` and
  `deflate_idempotent_canonical_roundtrip_inst` moved to `Stdlib/Zlib/RoundtripCorollaries.lean` as
  one-line corollaries of `deflate_roundtrip_soundness` (`Stdlib/Zlib/DynamicRoundtrip.lean:1457`), a
  real universal theorem over `∀ (data : ByteArray)`. The statements are byte-identical and are now
  backed by a ∀ proof. **This is exactly the right thing** and is real Law 9 progress.
- **One oracle swap.** The same commit prunes `spike3_empty_effect_trace_equivalence_inst`, described
  in its own message as "left behind by the spike `native_decide` retirement". The theorem's
  statement is unchanged; its domain is unchanged; it is a Schema I pointwise check that stopped
  carrying an axiom.

Both moved the score by the same amount per entry. **The score cannot distinguish them.** A plan
whose Rule 5 says no step counts as done until measured against `scripts/gate_allowlist.txt` before
and after will credit these identically.

### 2.3 Spike 1 is the existence proof, and it is already finished

Spike 1 has **four** whole-program contracts and **zero** allowlist entries. Commit `22041fe`
retired its `native_decide` occurrences to `decide` / `decide +kernel`. That commit's own message
states the position plainly: Spike 1's trace-equivalence theorems are "closed-term claims, not real
universals".

So the ledger already reports as fully clean a spike whose four contracts are all instantiated at
`Unit`, none of which says anything about any input. **The plan's goal is to make every spike look
like Spike 1.** Spike 1 is at zero and has fixed nothing.

### 2.4 What the ledger loses when an entry is retired this way

`scripts/gate_allowlist.txt` is the only place in this repository where the pointwise convention is
enumerated. Law 10 additionally requires that single-instance ground checks carry `*_inst` and
"MUST live in designated test/regression modules rather than on `Spec.lean`/`Equivalence.lean` proof
surfaces". `spike3_empty_effect_trace_equivalence_inst` still lives in
`Spikes/Spike3SortLines/Windows/Equivalence.lean`, is still cited by the whole-program contract, and
is now in no ledger. It moved from *tracked debt* to *untracked Law 10 placement violation*, and no
gate can see it.

### 2.5 The honest reading, stated fairly

The score is not worthless. The owner's target has three parts — "no axioms, strong verification,
checked models". A `native_decide` → `decide` conversion genuinely delivers the first: an axiom
leaves the trusted base, and Law 10 is right that rung 2 is categorically better than rung 3. What
the score cannot see is the second. **The allowlist measures 1 of the 3, and the plan treats it as
measuring all 3.**

### 2.6 The measurement that cannot be gamed

The count in §1's table — how many whole-program contracts bind their real input domain — is **0 of
18**, and no tactic swap can move it. `Gasm/Effects/ReadBinder.lean` and
`Gasm/Effects/ReadBinderWiring.lean` have landed and already contain the machinery to state it;
`spike4_unsafe_buffer_obligation_undischargeable` (`Gasm/Effects/ReadBinderWiring.lean:78`) is a
kernel-checked theorem that Spike 4's contract *cannot* be discharged at the honest domain.

So the tree simultaneously contains a proof that Spike 4's real obligation is undischargeable, and a
plan (B2–B4) to retire Spike 4's nine entries and report it clean.

---

## 3. Is spike-by-spike the right shape?

**No.** Three measurements decide it.

### 3.1 The obstructions are three classes, not one — and two are type choices, not proof problems

The brief asks whether "the kernel meets an opaque or non-reducing construct in a hook" is one
mechanism. Measured:

| target | obstruction | evidence | class |
|---|---|---|---|
| Spike 4, x86 | `recvHook` reaches `String.toUTF8` / `String.fromUTF8?`, both `@[extern]` | `Gasm/Targets/Windows/Win32API.lean:207-227` | **a field type** |
| Spike 5, codec | `Acc.rec` from well-founded recursion in `decompress` / `decodeHuffmanStream` | `Stdlib/Zlib/Deflate.lean` `termination_by` | a real reduction problem |
| all Wasm | *formerly* `mutual partial` compiling to an `opaque` constant | `Gasm/Targets/Wasm/Semantics.lean:189-210` | **already fixed** |
| Spike 3, x86 | none found | `readFileHook` (`Gasm/Targets/Windows/Win32API.lean:101-119`) is pure `ByteArray` | not blocked |

Two corrections to the plan follow, and both change dispatch:

- **Spike 4's blocker is `incomingRequests : List String`.** `recvHook` only touches `@[extern]`
  string conversions because the machine state's inbound queue is typed `List String` and must be
  converted to bytes and back on every delivery. B2 proposes two rewrite lemmas to reason *around*
  the conversions. **Changing the field to a byte type deletes the obstruction rather than
  routing around it**, needs no lemmas, and is required anyway: `docs/READ_BINDER_CONTRACT.md` §5 —
  the section `recvHook` itself cites — states the obligation over `bytes`, and Law 9's read-binder
  clause names `ByteArray` as the domain. `runWasiTraceState` (`Gasm/Targets/WASI/ABI.lean:215`)
  carries the identical `incomingRequests : List String` parameter, so **one change in `Gasm/` fixes
  the obstruction on two targets.** B2 as written is a workaround for a defect one layer down.
  **Status**: the field is `List String` today; no change proposed here is implemented.
- **The Wasm wall the plan does not name is gone.** `Gasm/Targets/Wasm/Semantics.lean` has been
  converted from `mutual partial` to fuel-based structural recursion, and its own docstring records
  that the `partial` group previously "compile[d] to an `opaque` constant with none [no defining
  equations]" and "blocked a proof outright". G1 was unschedulable while that held. It is
  schedulable now, and nothing in the plan records the change.

So: **the obstructions genuinely differ, exactly as the brief warned they might.** A single
trace-equivalence theorem spanning spikes would be the Law 8 mistake. That alternative is correctly
rejected.

### 3.2 But the leverage is one level lower, and the machinery already exists — dead

The population to attack at the language level is not the spikes. It is **the instruction set the
spikes are written in.** Measured over every spike `Program.lean` and `Stdlib/Zlib/X86_64.lean`:

| | distinct forms | occurrences |
|---|---:|---:|
| x86 data/arithmetic (`instr (…)`) | 34 | 2,053 |
| x86 control (`jmp_near_label`, `je_near_label`, `call_import`, …) | 9 | 412 |
| Wasm instructions | 30 | 529 |
| **total** | **73** | **2,994** |

Seventy-three total theorems — one per form, each `∀` over machine state and operands — cover every
program in the tree. This is precisely `docs/VISION.md` §4's operating rule ("anywhere there is a
population of artifacts — even a closed population… reach for a DSL"; "step lemmas and composition
rules are total theorems about the assembly DSL") and PLAN.md's D11.

**Twenty-seven of those theorems are already written, oracle-free, generic, and cited by nothing:**

| module | theorems | shape |
|---|---:|---|
| `Spikes/Spike3SortLines/Windows/InstructionStepLemmas.lean` | 20 | `step_mov_r64 (dst src : Reg64) (s : X86_64MachineState)` — per-opcode, ∀ over operands and state |
| `Spikes/Spike3SortLines/TraceStepLemmas.lean` | 4 | `runProgramTraceWithLoops_step_silent` etc., ∀ over program and state |
| `Spikes/Spike3SortLines/Windows/InterceptLemmas.lean` | 3 | `interceptCall_none_of_not_aligned` etc., ∀ over address |

All three are imported by `Spikes.lean` (so they compile) and cited by no proof anywhere.

### 3.3 The technique is not unproven — it has already closed a ∀ theorem about x86 execution

The plan states that these modules' "fitness is unproven" and makes C1 the pathfinder that
establishes it. **That is not correct.**
`Spikes/Spike2Fibonacci/Windows/Equivalence.lean:65` declares `fib_iter_asm_soundness (n : Nat)
(hn : n ≤ 124)` — a universally quantified statement about what the emitted x86 program computes —
and it is proven structurally, oracle-free, using `runProgramWithLoops_step` and
`runProgramWithLoops_stuck` from `Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean:357,374`. It
carries no allowlist entry.

So an x86 program-execution fact has already been retired from evaluation to induction, via
generic step lemmas, in this tree. The pathfinder the plan proposes to build has already run.

It also reveals a Law 12 defect the plan should absorb rather than repeat: `LoopInvariant.lean`'s
`runProgramWithLoops_step`/`_stuck` and `TraceStepLemmas.lean`'s
`runProgramTraceWithLoops_step_silent`/`_stuck` are two unlinked encodings of the same peeling fact,
in two spike directories, neither in `Gasm/`. Law 7 requires infrastructure to be relocated into
`Gasm` precisely so this does not happen; a third per-spike copy is what six more bespoke tracks
would produce.

### 3.4 What is actually missing

One thing, and the plan names none of it: **a composition lemma quantified over the program** that
chains per-step facts into a whole-trace fact, for `runProgramTraceWithLoops` and for
`runWasiTrace`. The step lemmas exist; the glue does not. `Gasm/Targets/X86_64/Semantics.lean`
carries 2 theorems in total. **Status**: no such composition lemma exists in the tree for either
trace interpreter.

### 3.5 Verdict on the shape

Spike-by-spike is wrong because it schedules 20-odd bespoke chains, each of which re-derives step
facts that 27 existing generic theorems already state, and none of which leaves anything reusable
behind. Hand-tracing Spike 4's measured 59 steps, Spike 3's unmeasured chain, Spike 5's five traces
and Spike 2's two is on the order of a few hundred ad-hoc step derivations against a population of
73 forms.

The plan's own construction admits this: it proposes C1 as a "pathfinder", which is an admission
that the work is meant to generalize — but it then routes the generalization through a spike
directory instead of through `Gasm/`, so it cannot.

---

## 4. The plan re-derives an analysis the repository already had

`docs/TRUST_PLAN.md` contains **no reference** to `docs/ORACLE_DEBT.md`, to `docs/VISION.md` §4, to
PLAN.md's D11 or Phase 4, or to any of PA1, PA2, PA3, PA5, PA6, PA7, PA8, PA9, PA15 or PA18. It
cites only PA16 and PA17.

What it re-derives or drops:

- `docs/ORACLE_DEBT.md` (2026-08-27) audited the same ledger, produced the shape taxonomy §1
  recovers, verified the propagation claim in its Part 5, named "what does not confidently reach
  zero" in its Part 4, and mapped every entry to a task. `docs/TRUST_PLAN_REVIEW.md` re-verified
  propagation at four points, and this review re-derived the shapes — both unaware.
- PLAN.md Phase 4 already schedules "Step-lemma library implementation… Composition calculus
  implementation" and names a **pathfinder**: the `crc32SymbolicProgram` ∀-proof, chosen because it
  is "small, loop-heavy, dual-implemented → connection theorem for free, **no syscalls**". The plan
  substitutes C1 — a large hand-trace, through syscall hooks, in a spike directory.
- PA6 → PA8 → PA9 is the designed structural answer to Schema I: make the contract bind `read`
  results universally, so a pointwise instantiation is unrepresentable. `Gasm/Effects/ReadBinder.lean`
  and `Gasm/Effects/ReadBinderWiring.lean` are landed first pieces of it. The plan schedules
  nothing that consumes them.

This is a Law 12 unlinked twin at the level of the plan: two parallel decompositions of one target,
with no connection theorem between them, and the newer one is the weaker.

---

## 5. Is zero the right target?

**Zero is achievable, and it is the wrong target — not because the number is wrong, but because the
quantity is.**

On achievability, the residue is genuinely 0. I found no entry whose subject is structurally outside
kernel checking. The `Emit.lean::main` and `Test.lean::main` entries carry whatever axiom their
contract carries and clear when it clears; they are not permanent. `docs/ORACLE_DEBT.md` Part 4's
two "may not reach zero" items have both moved: PA14 closed (`3ca668d`), and PA16's deflate half
landed as `deflate_roundtrip_soundness`. So "zero by default" is not the defect here.

The defect is that the plan's goal statement — "`scripts/gate_allowlist.txt` at zero" — is
satisfiable by §2.1's move on all 21 Schema I entries and their propagation, at which point the
ledger reads zero, the count is the score, and **not one contract binds its real input domain.**

**Proposed target, stated as two numbers rather than one:**

1. **Primary: whole-program contracts binding their real input domain — 0 of 18 today, target 18.**
   Mechanically derivable (read the `Env` type argument of each `Verified*Program` instantiation),
   immune to tactic substitution, and it is what ADR-0038 means by "the convention is the defect".
2. **Secondary: `scripts/gate_allowlist.txt` at zero**, retained as an honest axiom count — it
   measures the "no axioms" third of the owner's target and measures it correctly — but demoted from
   "the score" to one of two, and governed by the rule in §9.

---

## 6. Does the plan still contain the hedging pattern?

Yes, and it now has a second form.

**The named form, in the unscrutinised tracks.** The owner's criticism was of a step whose real
output is a satisfying number that is not the score.

| step | stated retirement | named consumer |
|---|---:|---|
| E5 (PNG status) | 0 | none — it is F1 restricted to two entries; the two steps duplicate |
| F1 (measure 18 obstructions) | 0 | none named; sequenced last, though it decides whether C/D/E are proof work or research |
| F2 (reconcile 78 vs 68) | 0 | resolved during this review at `a1cc4d1`; the ledger is exact |
| F4 (citation adequacy) | 0 | none; landed as `docs/CITATION_REVIEW.md`, valuable under Law 1, not progress toward this goal |
| G1 (WASI step lemmas) | 0 | C3 and two Spike 2 entries — a real consumer, and the step is now schedulable (§3.1) |
| G2 (assign 7 unowned entries) | 0 | bookkeeping the plan cannot complete as written (§7) |

E5 and F1 should be merged. F2 should be struck as done. F4 should be moved out of this plan — it is
Law 1 work, not Law 10 work, and Rule 5 cannot measure it. G1 is legitimate and should be re-scoped
now that its prerequisite has landed.

**The second form, which is larger: the plan as a whole has the hedge's shape.** A1's landing
recorded retirement zero and the plan calls that out honestly. But A1's *stated purpose* — "kills
Wall 1", where Wall 1 is defined as `decide` failing with reduction-stuck errors — is §2.1's move.
Track A's theory of change is: make kernel reduction succeed, so the pointwise checks can be
discharged by `decide`, so the entries disappear. That is not a zero-retirement step. It is a
**large**-retirement step by the route that fixes nothing, and the plan has not noticed which of the
two it is proposing. A2 is the same, one level up, and is correctly gated — but gated for the wrong
reason. The reason to gate A2 is not that its retirement is zero; it is that its retirement may be
large and worthless.

---

## 7. Are the 78 fully covered?

**No, and the plan is structurally unable to tell.**

The prior review found seven entries with no covering step. The current version adds **G2**, whose
content is "identify them precisely… and assign each to a track" — the gap is acknowledged and
converted into a step rather than closed. Until G2 runs, the retirement targets do not sum, and the
plan says so.

Two further reasons the sum cannot be trusted as written:

- **The denominator moved during the review** (78 → 73 on local `main`) with no step dispatched.
  Four of those five were found by an agent enumerating after finishing unrelated work. The plan has
  no step that sweeps for entries that have become corollaries of theorems already proven.
- **Double counting persists across tracks.** `Spikes/Spike5Gzip/Equivalence.lean`'s
  `gzip_roundtrip_soundness_inst` and `Stdlib/Zlib/Equivalence.lean`'s identically-named entry are
  the same proposition on different literals; A5 and E4 both claim them.

**The harvest pattern, tested rather than adopted.** The brief asked me to test whether "theorems get
proven and entries that could become their corollaries are never rewritten" generalises. It
partially does:

- **It does not extend to the four remaining `Stdlib/Zlib/Equivalence.lean` entries.** `zlib_*` and
  `gzip_*` roundtrips need container-level framing theorems, and **there are none** — a grep for
  non-`_inst` theorems naming `zlib` or `gzip` across `Stdlib/Zlib` returns nothing. These are
  NEEDS-THEOREM, not harvestable.
- **It plausibly extends to PNG.** `filter_unfilter_soundness (ft raw prior bpp)`
  (`Stdlib/Png/Equivalence.lean:344`) is universal and oracle-free, and sits 23 lines above
  `png_roundtrip_soundness_inst`, which is not. **Status**: I did not attempt the connection, and the
  whole-image roundtrip also routes through zlib, so this is a candidate, not a finding.
- **The general lesson holds even where the specific harvest does not**: the plan has no step that
  re-checks the enumeration against newly-landed theorems, and the single largest score movement of
  the campaign came from doing exactly that by accident.

---

## 8. Is the propagation claim safe to build on?

**No — it is false as stated, and the failure is a whole class, not an accident.**

The claim is that `axiom-only` entries are propagation from `grandfathered` roots, so retiring a root
cascades. Tested where it is least likely to hold — at roots that no whole-program contract consumes:

- **All 11 of Spike 5's `axiom-only` entries cite trace equivalences. None cites either `_inst`
  roundtrip.** Retiring `Spikes/Spike5Gzip/Equivalence.lean`'s two Schema II roots cascades to
  nothing.
- **`Stdlib/Zlib/Equivalence.lean` and `Stdlib/Png/Equivalence.lean` contribute zero `axiom-only`
  entries between them.** All ten of their roots (now six, after `f2b4bf3`) are terminal by
  construction — nothing downstream cites them.

The pattern is not random: **Schema II roots are terminal; Schema I roots cascade.** A codec
roundtrip on a literal is cited by nothing because nothing is built on it; a trace equivalence is the
field of a whole-program contract that `Emit.lean` and `Test.lean` consume.

Consequences for the plan's leverage argument: the concentration is real but is concentrated
differently than stated. Roughly, the 21 Schema I roots gate the 44 `axiom-only` entries; the 8
Schema II roots gate themselves. The plan's "Spike 4's 9 roots gate 21 entries" is the right shape;
"Stdlib codec entries: retires 8" is 8 and not one more.

The first review's four verification points were all Schema I. **Status**: I did not build the full
bipartite map; the two findings above are the cases I checked, and the schema-based explanation is a
hypothesis that the map would confirm or refute.

---

## 9. Law 13 — is anything being solved that would be better prevented?

Yes, and ADR-0038's own order of operations tells us when.

ADR-0038 rules that the ratchet gate is not built now: reduce, demonstrate, then ratchet. That
ruling is correct and should stand. But it was written about a **count** ratchet, and §2 shows a
count ratchet would not have caught the thing that actually needs preventing. Three cheaper gates
are available, in increasing order of what they would cost us to meet first:

1. **Fail on retiring a Schema I entry by oracle swap.** Mechanically: a declaration whose name ends
   `_inst` may not sit in a `Spec.lean` or `Equivalence.lean`. This is Law 10's existing placement
   rule, unenforced, checkable by name suffix and module path, and blind to which tactic closed the
   proof. `spike3_empty_effect_trace_equivalence_inst` violates it today. **We do not meet this
   standard yet**, so under ADR-0038 the order is: relocate the `*_inst` checks, then gate.
2. **Fail on citing an `*_inst` declaration.** Law 10 says single-instance checks "MUST NOT be cited
   — in names, docs, or review artifacts — as evidence that anything is verified", and every
   whole-program contract in the tree cites one. This is the most valuable gate and the furthest from
   being met; it becomes available only when contracts stop being filled by pointwise proofs, which
   is PA6/PA8/PA9's deliverable.
3. **Report the primary metric.** `Tools/CheckGatesAxioms.lean` already emits a count; a sibling
   walk that prints "contracts binding their real input domain: 0 of 18" costs little, needs no
   enforcement, and cannot be gamed. **This one imposes nothing on anyone and can land immediately** —
   ADR-0038's bar does not apply to a number that fails nothing.

The treadmill the brief asks about is real but is not the one it names. The mint is not producing new
entries — it produced four in the other team's merge, and the count has fallen since. The treadmill
is that **retiring an entry is currently cheaper by the route that fixes nothing**, so effort flows
there under any plan whose score is the count.

---

## 10. The single highest-leverage change to the plan

**Split the ledger by schema, score them separately, and add one rule: a Schema I entry may be
retired only by widening its domain, never by swapping its oracle.**

One change, and it re-sequences everything downstream:

- It makes §2.2's two retirements land in different columns, so the plan stops crediting them
  equally.
- It makes A1/A2's real theory of change visible, which is what the owner's "hedging" criticism was
  reaching for and could not name.
- It re-points Track B from "two rewrite lemmas around `recvHook`" to "change `incomingRequests` to a
  byte type in `Gasm/`", which is smaller, fixes two targets, and is required by Law 9 regardless.
- It makes the 27 dead generic lemmas the obvious next investment, because under the Schema I rule
  the only way forward is a ∀ proof, and a ∀ proof over a 73-form instruction population is a
  language-level job.
- It reconnects the plan to PA6/PA8/PA9 and `docs/ORACLE_DEBT.md`, so the second decomposition stops
  competing with the first.

If only one smaller thing can be done instead: **strike "the goal is `scripts/gate_allowlist.txt` at
zero" from line 6** and replace it with the two numbers in §5. Every defect in this review descends
from that sentence.

---

## 11. Law bearing

- **Law 9** — the anti-pointwise law is the law this plan is trying to satisfy and the law its score
  cannot see. §2, §5.
- **Law 10** — rung 2's "no allowlist entry at all" is correct and is also the escape hatch. The
  placement and non-citation clauses are unenforced. §2.4, §9.
- **Law 12** — two unlinked plan decompositions (§4); two unlinked step-peeling lemma sets (§3.3).
- **Law 13** — three findings here should become gates, in ADR-0038's order. §9.
- **Law 7** — 27 generic lemmas sit in spike directories; Law 7 requires infrastructure to be
  relocated into `Gasm`. §3.3.
- **Law 5** — B2 proposes lemmas to work around a field type that `docs/READ_BINDER_CONTRACT.md` §5
  already specifies differently. Stop-and-design applies. §3.1.
- **Law 8** — a single trace-equivalence theorem spanning spikes would be the premature abstraction
  this law forbids; the obstructions genuinely differ (§3.1). The step-lemma library is not that
  mistake: 27 instances of it already exist and one ∀ theorem has already been closed with the
  technique (§3.3).
- **ADR-0037 / Law 10 rung 4** — untouched. `bv_decide` is at zero occurrences tree-wide and nothing
  here reopens it.
- **`docs/REVIEW.md` §4.2 C** — this review cites documents and mechanisms rather than declarations
  under test, so it produces no Citation Adequacy Table. The one citation it does judge is
  `recvHook`'s `REF:` to `docs/READ_BINDER_CONTRACT.md` §5, classified **understated**: the section
  states the obligation over `bytes`, and the declaration's own state field is `List String`.
