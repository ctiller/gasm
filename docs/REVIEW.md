# Repository Citation Laws, Bidirectional Traceability & Review Protocol

This document establishes the **Citation Laws**, **Repository Invariants**, and **Bidirectional Review Protocol** governing all Lean 4 source code, spikes, and markdown design specifications in `gasm`.

---

## 1. The Core Citation Syntax: `/- REF: ... -/`

Every top-level Lean 4 item (including `inductive`, `structure`, `def`, `class`, `instance`, `theorem`, `lemma`, and `axiom`) **MUST** have one or more `/- REF: ... -/` annotations attached directly above the declaration:

```lean
/- REF: docs/API_STATE_MODELS.md#1-the-composed-state-model--zero-cost-proof-erasure -/
structure ComposedState (Arch : Type) (ApiStateType : Type) where
  machine     : MachineState Arch
  stackDepth  : Nat
  api         : ApiStateType
  perms       : MemoryPermissions Arch
  obligations : List Obligation
  causalClock : VectorClock
```

### 1.1 Citation Format Rules
- **Path Target**: Path relative to repository root (e.g. `docs/API_STATE_MODELS.md` or `references/intel_sdm/...`).
- **Section Anchor**: Standard github markdown heading anchor (e.g. `#1-the-composed-state-model--zero-cost-proof-erasure` or `#2-multi-abi-calling-conventions--stack-restoration-laws`).
- **Multiple References**: When a Lean item synthesizes multiple specification concepts, multiple `/- REF: ... -/` annotations are placed in sequence:
  ```lean
  /- REF: docs/STACK_DISCIPLINE.md#2-multi-abi-calling-conventions--stack-restoration-laws -/
  /- REF: docs/EQUIVALENCE_PROOFS.md#42-theorem-2-callability--abi-preservation-caller-consumer -/
  theorem memcpy_callability [abi : AbiDiscipline Arch ABI] : ...
  ```

---

## 2. The Repository Citation & Design Laws

### Law 1: Complete Traceability & Strict Derivation (No Invention)
> **Every Lean item is *COMPLETELY* defined and motivated by its attached `REF:` notes.**

- A Lean declaration cannot introduce concepts, fields, invariants, or behaviors that are not specified in the referenced markdown sections.
- If an implementation detail is needed that was not anticipated in the design doc, the design doc **MUST be updated and reviewed first** before the Lean code is written.
- Un-cited code is strictly prohibited in the codebase.

### Law 2: Implementation Completeness (100% Realization)
> **Once a markdown section is referenced by any Lean `REF:` annotation, that section MUST be 100% implemented by the Lean codebase.**

- Partial implementation of a referenced section is treated as a critical bug.
- If a section defines a data structure, helper lemmas, and an equivalence theorem, referencing that section obligates the author to implement the data structure, all helper lemmas, and the theorem.
- Anything specified in a referenced section that is omitted from the Lean implementation fails code review.

### Law 3: Automated Coverage & Unreferenced Backlog Tooling
> **All markdown sections that have not yet been referenced represent the *Unimplemented System Backlog*, which MUST be automatically tracked by tooling.**

- The repository provides two independent, automated verification tools -- see §4.1.2 for why declaration coverage was split out of `scripts/check_refs.py` into its own compiled-environment-driven tool rather than staying a second job for the same regex-based script:
  1. `scripts/check_refs.py` parses all markdown files in `docs/` and `references/` and indexes all section headings; parses all `.lean` files and indexes all `/- REF: ... -/` citations via a plain regex scan (no declaration parsing at all); validates that every `REF:` target points to a valid existing section or registry entry (failing CI on broken references, Law 3 item 3 below); and computes and reports the list of **Unreferenced Markdown Sections** (the remaining implementation backlog, Law 3 item 4 below).
  2. `lake exe check_refs_coverage` (`Tools/CheckRefsCoverage.lean`) detects any Lean declaration lacking a `REF:` annotation (failing CI on un-cited code, Law 1) by walking the COMPILED ENVIRONMENT rather than source text, so no declaration syntax form can hide from it.

### Law 4: External Reference Ingestion Law (No Self-Authored Standards)
> **Official reference documentation (e.g. Intel/AMD ISA manuals, Microsoft PE/COFF specification, Windows Win32 API contracts) must be brought into the repository directly as authoritative sources.**

- We do NOT author or synthesize ad-hoc approximations of hardware manuals or external OS specifications; that is a massive cheat.
- Authentic, authoritative reference texts must be imported/vendored directly into the repository so that formal models cite genuine ground truth.

### Law 5: The Stop-and-Design Invariant
> **Whenever a spike or implementation task demands any concept, instruction, ABI rule, binary header, or API contract that is not yet fully designed in the repository, implementation MUST STOP immediately.**

- The missing specification must be authored, reviewed, and committed to `docs/` before any Lean code for that task is written.

### Law 6: Reference Reproducibility Mandate
> **Every external document a Lean declaration cites MUST be a hash-pinned, independently-refetchable entry in `references.json`, not vendored prose in the tree.**

- **This law's mechanism changed on 2026-08-27** (`PLAN.md`, the `references/`-deletion task): the vendored `references/` corpus tree, `references/MANIFEST.{provenance.json,sha256}`, and `scripts/regenerate_references.py` (the script that generated and verified that tree, and the entire "snapshot-reproducibility" model described in this law's older revisions) are **deleted**. The owner's ruling was unconditional -- zero third-party prose in the tree at publish, independent of redistributability -- so this is not a narrowing of Law 6's old exception list, it is a different mechanism entirely: no corpus is vendored at all any more.
- **Current mechanism:** every citable external source is one entry in `references.json` (repo root) -- `slug`, `url`, `sha256` of the exact bytes last fetched, `license`, `distribution`, `anchor_mode`, and a reviewer/review_note trail. A Lean `REF: <slug>#<anchor>` citation (docs/REFERENCE_INDEX.md) is checked by `python scripts/check_references.py --offline`: the slug must be registered, its `.cache/references/<slug>.<ext>` cache file's *freshly recomputed* SHA-256 must match the recorded pin (never a stored-number-to-stored-number comparison), and the anchor must resolve under its `anchor_mode` grammar against that cached content. `--refresh` (network) re-fetches a target's `url`, recomputes SHA-256, and either promotes the fetch into the cache (match) or hard-stops reporting drift (mismatch) -- a hash is never silently rewritten; only `--acknowledge-drift --reviewer ... --review-note ...` can re-pin, and it leaves an attributed trail.
- **Known operational gap, not silently dropped (`docs/CI.md` #7):** `--offline`'s cache is local and gitignored (`.cache/references/`, never committed); no CI step currently runs `--refresh` to populate it, so `--offline` fails on a cold cache in a fresh checkout today. Closing this needs the scheduled-refresh + staleness-bound design `docs/CI.md` #7 describes, which is designed but not yet implemented. This is a gap in *keeping the gate green automatically*, not in the registry's own integrity model: every entry in `references.json` today was independently fetched and hash-verified at registration time (see each entry's `review_note`).

### Law 7: Target Separation & Equivalence Proof Purity (The Authoring Ergonomics Mandate)
> **The primary objective of `gasm` is that it MUST be clean and effortless to author the core trio: `Spec.lean`, `Program.lean`, and `Equivalence.lean`. Architects and contributors must actively work to minimize distractions and boilerplate in that trio by aggressively relocating infrastructure responsibilities into `Gasm` itself.**

- **Target Completeness**: The target machine model and execution semantics (`Gasm.Targets.*`) are strictly responsible for program loading, instruction address resolution, instruction fetching, stack/register initialization, and control flow traversal (branches, loops, jumps, calls, returns).
- **Proof Role**: Equivalence proofs (`Equivalence.lean`) exist solely to state and prove semantic correspondence between high-level specification traces and lower-level target machine executions.
- **Relocation of Responsibilities**:
  1. *Pure Specifications (`Spec.lean`)*: Express mathematical domain logic and portable effect intents without premature lowerings or machine-specific baggage.
  2. *Idiomatic Programs (`Program.lean`)*: Represent straightforward, idiomatic assembly/AST declarations without manually calculating byte offsets or encoding details.
  3. *Pure Equivalence Proofs (`Equivalence.lean`)*: Prove simulation relations without defining ad-hoc interpreters, manual state setup shims, or jump resolution tables.
- **Prohibited Proof Anti-Patterns**:
  1. *Manual Jump/Offset Tables in Proofs*: Mapping `s.rip` offsets to instruction indices inside proof files (e.g. `if offset == 0 then 0 else if offset == 2 then 1...`) is strictly rejected. Targets MUST provide dynamic instruction fetch and looping interpreters based on actual encoded byte lengths (`instructionAtRip`).
  2. *Hardcoded Target Machine/Layout Constants*: Hardcoding machine layout constants (e.g. ad-hoc `rip := 0x1000`, arbitrary stack pointers) in lieu of target loaders or platform ABI setup.
  3. *Target Implementation Substitutions*: Equivalence proof files must NEVER act as a polyfill or workaround for missing target capabilities. Any required execution behavior must be properly implemented in the target architecture layer first.

### Law 8: Semantic Spec-to-Code Fidelity & Anti-Facade Law (No Dead Abstractions or Mock Verification)
> **Every abstraction, typeclass, and API contract defined in a design specification MUST be actively invoked and semantically realized in the functional execution path of the implementation. Facades, uninvoked typeclasses, and inert abstractions are treated as critical defects.**

- **No Inert Abstractions / Dead Typeclasses**: If a specification mandates parameterization over an abstraction (e.g. `PageSource` with `fetchPages`), the implementation MUST actually invoke that typeclass method in its operational execution path when the contract demands it. Defining a typeclass and then implementing functions that bypass or ignore it is strictly prohibited.
- **Universal Specification Theorems vs. Concrete Simulation Instances**:
  - Theorems claiming to prove specification properties (e.g., obligation conservation, freelist reuse, dichotomy) MUST be universally quantified ($\forall$) over arbitrary valid inputs and states.
  - Ground instances evaluated on concrete values via `by decide` are simulation tests and must be explicitly labeled as such (`*_inst`), never presented as general soundness theorems.
- **Audited Observable Tracing for External Subsystems**: Where interaction with external subsystems (OS APIs, allocators, peripherals) is modeled, formal theorems MUST prove that observable effects or calls (e.g., `VirtualAlloc`, `WriteFile`) actually occur in the execution trace.

### Law 9: Universal Quantification & Input Completeness Mandate (The Anti-Pointwise Law)
> **Whole-program verification contracts (`VerifiedProgram`, `VerifiedWasmProgram`) MUST be universally quantified across all valid environment inputs $\forall (env : Env)$. Pointwise verification over single hardcoded test vectors is strictly prohibited.**

- **No Single-Point Bypasses**: Instantiating a whole-program contract with a static, hardcoded sample vector (e.g. testing only a fixed 63-byte buffer) and asserting equivalence solely on that point constitutes mock verification and fails code review.
- **Dynamic Syscall Soundness**: Any binary program that queries the operating system via syscalls (`ReadFile`, `recv`, `fd_read`) must mathematically prove that for **all possible byte buffers** returned by the host environment, its machine code computes the exact transformation mandated by the high-level specification.
- **Genuine Algorithmic Realization**: Low-level machine subroutines (compression, sorting, tokenization, serialization) must implement the actual algorithmic state transitions in machine code (e.g. dynamic sliding-window searches, bitwise Huffman bit-packers, in-place pointer swaps), rather than falling back to uncompressed passthrough wrappers or hardcoded literals.
- **`read` is the universal binder (the enforcement vector for this law)**: every monadic input operation in a specification (`readFile`, `recv`, `accept`, console reads — all forms of `read`) binds an arbitrary result, and the verification contract MUST be parametric in that result: the continuation after a read is proven correct for **any** returned `ByteArray` — any contents, any length, including partial reads, empty reads, and EOF. Contracts that pin a read's result to a concrete vector are unrepresentable as verified. Because `read` may return any chunking of the input, robustness to input chunking is itself a forced universal obligation — the input-side dual of the output coalescing congruence (`docs/SYSTEM_EFFECTS.md` §6.1, §6.4). **Status**: closing the three known evasion shapes this way — hardcoded-output stubs (a spec that reads cannot be satisfied by a constant), domain-shrinking via purpose-built input enums (the read binds the real byte-array domain), and pointwise evaluation (no evaluator can discharge a claim over a bound variable) — is what this contract shape delivers ONCE implemented; it is not a description of current enforcement. No contract in the tree binds `read` this way today: every `VerifiedProgram` closes over a free `Env`, and Spike5's operations quantify over a one-constructor enum rather than a real byte-array domain. Enforcement is tracked as PA6 (`docs/tasks/PA6-read-binder-contract.md`); until PA6 lands, this bullet is the standard new contracts are reviewed against, not a report of what current contracts already do.

### Law 10: Kernel-Checked Gates & the `native_decide` Restriction (Exhaustive Finite Domains Only)
> **A verification obligation may be discharged by `decide`, `native_decide`, or `bv_decide` if and only if the proposition is universally quantified over its entire, finite domain — the three are admissible in the same restricted sense, at ascending trust cost (rungs 2–4 below). Any of the three on a single ground instance — or on any proposition whose input domain is infinite or merely sampled — can NEVER satisfy a verification obligation.**

This Law orders proof mechanisms by trust cost, not by convenience. Four rungs:

1. **Structural proof** (induction, algebraic rewriting, composition of routine contracts). No oracle of any kind — the kernel checks the proof term directly. Always preferred, regardless of domain size.
2. **`decide`**. The *kernel itself* performs the evaluation as part of type-checking; no axiom is introduced, so a `decide` occurrence needs no `scripts/gate_allowlist.txt` entry at all — the kernel's own check already is the gate. This rung is categorically different from rungs 3 and 4, not merely a cheaper version of the same trust: it is genuinely kernel-checked, they are not. Feasible only on domains small enough for the kernel's own evaluator to walk directly.
3. **`native_decide`**. Trusted, not checked: Lean's compiler and runtime evaluate the decision procedure as compiled native code, and the boolean result is asserted into the environment as a fresh axiom rather than replayed by the kernel. Requires the domain to be enumerable at compiled-execution speed.
4. **`bv_decide`**. The same trust class as rung 3 — confirmed by reading the mechanism, not inferred from the name (`TCB.md` T14): `LratCert.toReflectionProof` calls the identical `Lean.Meta.nativeEqTrue` routine `native_decide` itself calls, to compile and run an LRAT-certificate checker, then asserts the result as a declaration-local axiom; the kernel never replays the certificate. Its trusted surface is strictly larger than rung 3's — it additionally trusts the bitblaster and the external LRAT checker — but it reaches finite bitvector domains far too large to enumerate at rung 3's pace. `crc32ByteStep_eq_G8` (`Stdlib/Zlib/CRC32Equivalence.lean`) is the concrete case: it is universally quantified over `UInt32 × UInt8`, roughly 10^12 cases — not merely slow to enumerate but infeasible — so for that theorem the real choice was `bv_decide` or no proof at all, not `bv_decide` versus a cheaper rung.

- **Rationale**: Implementations are generated by untrusted, creative processes ([`docs/VISION.md`](VISION.md#2-the-consequence-the-validation-gate-is-the-product)). A gate that examines sampled points is adversarially unsound: an implementation specialized to those points passes it while being wrong everywhere else — this is why every rung above requires exhaustiveness over the domain, never sampling.
- **Exhaustive finite-∀ is acceptable at rungs 2–4**: propositions quantified over a complete finite domain (all 256 byte values, all 16×16 register pairs, every constructor of an input enum, the complete `UInt32 × UInt8` domain) may be discharged by whichever of `decide`/`native_decide`/`bv_decide` can actually reach that domain; for exactly these exhaustive checks the corresponding evaluator is admitted into the trusted base.
- **The finite domain must be the specification's actual input domain** (or an exhaustive cover of it) — exhaustiveness over a purpose-built stand-in (a single-constructor enum, `Unit`, a shrunken index type) is domain-shrinking under Law 9 and remains prohibited at every rung; Law 10 never licenses what Law 9 forbids. The ~25 existing spike contracts of this shape are grandfathered migration backlog (PA8), not compliant instances.
- **Single-instance ground checks are regression tests, not verification**: they MUST carry the `*_inst` suffix (Law 8), MUST live in designated test/regression modules rather than on `Spec.lean`/`Equivalence.lean` proof surfaces, and MUST NOT be cited — in names, docs, or review artifacts — as evidence that anything is verified. This applies uniformly across rungs 2–4.
- **Infinite-domain claims require structural proof**: ∀ over `ByteArray`, `Nat`, or arbitrary machine states is discharged only by kernel-checked structural proof (rung 1: induction, simulation arguments, composition of routine contracts per [`docs/VISION.md`](VISION.md#4-tractability-modular-contracts-composed-proofs)). No compiled evaluator, bit-blasted or otherwise, reaches an infinite domain honestly.
- **Rungs 3 and 4 require an honest allowlist entry; rung 2 does not**: any `native_decide` or `bv_decide` occurrence must carry a matching `scripts/gate_allowlist.txt` entry under an honest category (`finite-forall`, `grandfathered`, or `axiom-only` — see §4.1.1); a bare `decide` introduces no axiom, so the load-bearing gate (`lake exe check_gates_axioms`, which walks kernel-recorded axiom dependencies) has nothing to catch there. `scripts/gate_allowlist.txt`'s four PA1 `bv_decide` entries in `Stdlib/Zlib/CRC32Equivalence.lean` (`and_one_cases`, `G_eq_Gbf`, `xor_byte_shr8`, `G8bf_table`) remain categorized `finite-forall`, unchanged by this ratification (`TCB.md` T14 recommends no change): each is an ordinary theorem universally quantified, via typed parameters, over a complete finite bitvector domain, reviewed on the same grounds as any other exhaustive `decide`/`native_decide` proof, not on a `bv_decide`-specific exception.
- **Solver-version disclosure (T14)**: `bv_decide` resolves an external CaDiCaL-compatible SAT solver — `cadical.exe` from the toolchain's own `bin/` directory when present, pinned by `lean-toolchain` the same way `lean.exe`/`lake.exe` are, or a bare `cadical` on `PATH` otherwise, which is unpinned by construction — to search for the LRAT certificate that rung 4's native-eval step then trusts. `scripts/run_gates.py`'s `detect_cadical()` records which of the two was actually resolved, and its version string, in the same oracle-version table TCB T9 already maintains for `node`/`nasm`/`python`.
- **Tooling obligation (backlog)**: the CI linter must enumerate every `native_decide`/`bv_decide` occurrence and verify it is either in a designated regression module or attached to an exhaustive finite-∀ proposition.

**Status**: ratified 2026-08-27 (`PLAN.md` D28; [ADR-0037](adr/0037-ratify-bv-decide-trust-tier.md)). This supersedes the `bv_decide` wording previously marked `**Status**: proposed` in this section. The owner's approval was of `bv_decide`'s admissibility under this Law's existing restriction; the four-rung ordering above is the coordinator's framing of the trust-cost distinctions `TCB.md` T14 established, which the owner assented to but did not author verbatim — see the ADR's Provenance section. Rung 4 is admitted as a waypoint, not a destination: the owner's separately-stated target ("a trustable state: no axioms, strong verification, checked models") makes every allowlist entry at rungs 3–4 recorded debt against an eventual zero, not a compliant resting place — see the ADR's Consequences section.

### Law 11: Memory Access Capability Mandate (Fail-to-Assemble)
> **Every instruction that reads or writes memory MUST carry proof of a valid, in-scope capability (`MemoryPerm`) covering the accessed range. Program construction MUST fail — the artifact must be unbuildable — when that proof is absent.**

- **Memory safety is foundational, not advisory**: it is enforced at authoring/assembly time by construction, never audited after the fact.
- **The Core capability machinery is the authoring surface**: `MemoryPermissions`, permission tokens, obligation ledgers, and the `BlockM` typestate monad are the mandated path for memory-touching programs. Authoring paths that bypass them (raw symbolic memory operands with no attached capability) are prohibited in migrated modules; unmigrated modules are tracked as critical backlog, and new programs MUST NOT be authored on the bypass path.
- **Capabilities double as frame conditions**: the token that authorizes an access also delimits the routine's memory footprint, enabling modular equivalence proofs that compose without global reasoning.
- **Bounds are contracts**: fixed-size regions (arenas, I/O buffers, scratch spaces) must have their bounds represented as capabilities so that overrun is *unrepresentable*, not merely untested.
- **Status**: zero modules are migrated to the capability-authoring path today; migration is tracked as PA4 (`docs/tasks/PA4-capability-adoption.md`). The law binds new authoring immediately and the migration backlog going forward — it does not describe present code. Any claim that current artifacts satisfy this law is false.

### Law 12: Connection Theorem Mandate (No Unlinked Twins)
> **Two encodings of the same model-level fact (a table and a closed-form function; a pure-Lean algorithm and its assembly realization's inlined constants; parallel encoders) may coexist ONLY when linked by a kernel-checked connection theorem proving their equivalence. Unlinked duplication of model-level facts is a critical defect.**

- **Preference order**: (1) a single source of truth from which other forms are derived; (2) where genuine re-encoding is necessary (e.g. an assembly branch tree mirroring a lookup table), a connection theorem proving equality over the entire (finite) shared domain; (3) anything else fails review.
- **Tooling obligation (backlog)**: a linter (sibling of `check_refs.py`) detects likely unlinked twins — repeated literal tables, repeated byte-string constants, parallel same-shape definitions — and fails CI unless each detected pair is covered by a registered connection theorem.
- **Review protocol on top (belt and braces)**: Pillar 3's Factoring & DRY axis explicitly audits for semantic duplication beyond what literal-matching tooling can see; deterministic prioritization of likely duplicates (e.g. embedding-model similarity over declaration bodies) is an anticipated tooling extension for review-time triage.

### Law 13: Findings Become Gates (The Ratchet Law)
> **Every defect found by review, fuzzing, or debugging MUST terminate in a mechanical prevention — a construction that makes the class unrepresentable, a kernel-checked theorem, a build-failing check, or a mandatory oracle control vector — that would have caught the defect's entire class automatically. Fixing the instance without mechanizing the prevention fails review.**

- **A reviewer catching a bug is evidence of a missing gate, not of a working process.** The purpose of this project is mechanical verification; human and agent review exists to find the gaps in the gates, and each finding must close its gap, not just its instance.
- **Preference order for the mechanization**: (1) unrepresentable by construction (types, mandatory typeclass fields, derivation instead of duplication); (2) kernel-checked theorem discharged at build time; (3) build-failing linter or environment audit; (4) for harnesses that interact with the world (hardware, engines, OS) and therefore cannot be theorems: mandatory **positive and negative control vectors** at the start of every session — the oracle must demonstrably pass a known-good input AND reject a known-bad input before any of its results count, and a control failure aborts the run. An oracle that cannot run must fail the run; it must never no-op, skip, or synthesize results.
- **Check ∀, fix ∀**: a pointwise prevention (a sentinel case, a control vector) is acceptable only where the *world itself* is being sampled (is the engine present, is the CPU behaving). Wherever the artifact is under our control, the prevention must be ∀-shaped: validity proven for every emittable artifact (e.g. a typechecker plus a build-time theorem that every registered test module validates), or the failure state made unrepresentable in the types (e.g. oracle outcomes as an `Except` that no code path can synthesize). Fixing the three broken instances of a class while leaving the class constructible fails review.
- **Review sign-off must name the gate**: every fix lands with either the new mechanical gate that prevents its class, or a citation of the existing gate that should have caught it and an explanation of why it did not (which is itself a finding against that gate).

### Law 14: Calibration Data Governance (The Third Reference Class)
> **Measured data about this machine — timings, bandwidths, latencies, and any coefficient derived from them — is governed as a third reference class, distinct from Law 4's vendored specifications and Law 6's upstream-reproducible corpora. It MUST be checked in, regenerable by a committed harness, provenance-stamped, and never hand-edited; a model coefficient MUST cite its calibration file rather than carry a bare literal.**

- **Why a third class**: Law 4 governs authoritative text we did not write; Law 6 binds `references/` by name and requires reproducibility *from an upstream*. Measurement has no upstream — it is reproducible only by re-running a harness on stated hardware — so calibration data satisfies neither law and would otherwise sit in a gap between them.
- **The failure being prevented is documented history**: this project's predecessor recorded RDTSC medians as hand-transcribed `Nat` literals in source, which then rotted silently (two different kernels frozen at the same measured value). Every requirement below exists to make that specific rot detectable.
- **Regenerable, not transcribed**: every calibration artifact is paired with the committed harness that produces it, and its provenance records the harness commit. Hand-editing a measured value is prohibited and must be *mechanically detected*, not merely discouraged: artifacts store raw samples plus a committed pure reduction function, and the gate recomputes the reduction and fails on mismatch.
- **Provenance is mandatory and machine-checkable**: named device profile, host fingerprint, frequency/power policy, OS build, tool versions, run conditions, and the outcomes of the session's control vectors (Law 13) are recorded *in the artifact*. A file that cannot show its controls ran is not evidence.
- **Staleness is keyed on the measured subject**, not on one file's history: freshness is a function of the harness's transitive source closure and an explicit list of what was measured. A calibration file whose subject changed is stale even if the harness did not.
- **Recalibration is an explicit re-baseline**: artifacts carry a generation identity, and consumers record the generation they were authored against, so a new measurement cannot silently re-evaluate existing cost contracts.
- **Coefficients cite, they do not copy**: a model constant traceable to measurement must be bound to its calibration artifact by a mechanical check; a bare literal with a prose citation is the prohibited shape.
- **Honesty in output**: gate and report output states how many microarchitectures a model has actually been validated on, and coefficients validated by neither a vendored source nor a discriminating measurement are marked model-internal and may not be cited as facts.
- **Gate**: `python scripts/check_calibration.py` — **not yet implemented and not yet
  registered in §4.1 Pillar 1's enumerated list** (F2's design is still under revision;
  see `docs/tasks/F2-calibration-data-governance.md`, status `designing`). This line
  previously claimed present-tense registration that did not hold; `docs/CI.md` §7
  flagged the drift. Add it to §4.1's numbered list and wire it into
  `scripts/run_gates.py` and CI in the same change that lands the script.

---

## 3. Bidirectional Traceability: The Many-to-Many Mapping

Real-world verified software rarely maps 1-to-1 between documentation sections and code declarations. `gasm` enforces **Bidirectional Traceability**:

```
Markdown Specification Sections               Lean 4 Formal Declarations
+-----------------------------+               +----------------------------+
| docs/API_STATE_MODELS.md#1  | <-----------> | ComposedState              |
+-----------------------------+       \       +----------------------------+
| docs/STACK_DISCIPLINE.md#2  | <---+  \----> | PermissionShare            |
+-----------------------------+     |         +----------------------------+
| docs/EQUIVALENCE_PROOFS.md#4| <---|-------> | AbiDiscipline              |
+-----------------------------+     \         +----------------------------+
                                     \------> | memcpy_callability         |
                                              +----------------------------+
```

1. **One Section $\to$ Many Lean Items ($1 \to N$)**:
   - Implementing a section like `docs/API_STATE_MODELS.md#4-basicblock-structure--target-parametric-terminators` naturally requires defining `TargetArch`, `BasicBlock`, `CpuTerminator`, and individual constructor soundness lemmas.
2. **Many Sections $\to$ One Lean Item ($M \to 1$)**:
   - A top-level equivalence theorem like `memcpy_callability` combines stack frame restoration (`STACK_DISCIPLINE.md`), ABI register preservation (`TARGETS/X86_64.md`), and simulation relations (`EQUIVALENCE_PROOFS.md`). It carries `REF:` notes to all relevant sections.

---

## 4. The Three-Pillar Verification Protocol

A pull request or codebase component is evaluated through a strict synthesis of mechanical compiler truth, adversarial semantic auditing, and structured architectural evaluation. **Qualitative, hand-wavy reviews (e.g., "LGTM") are strictly prohibited.**

**North star**: the one question review can never delegate is *are we proving the right theorems?* (Pillar 2 — spec-to-theorem fidelity and domain-gap hunting). Pillars 1 and 3 exist to be progressively absorbed into mechanical gates (Law 13); any Pillar-1/3 finding a reviewer makes by hand is simultaneously a defect report and a missing-gate report.

### 4.1 Pillar 1: Mechanical Truth (Automated CI Gates)
The Lean 4 compiler provides the absolute baseline of logic. If any of the following fail, the PR is instantly rejected:
1. **Type & Proof Integrity:** `lake build` must pass with zero `sorry` and zero un-authorized axioms.
   - *Liveness:* Verified routines must provide existential liveness (`progressProof`) preventing instant-termination vacuity. **Status**: no contract in the tree today defines or requires a `progressProof` obligation -- `progressProof` does not exist anywhere in `Gasm`/`Stdlib`/`Spikes`, and no `VerifiedProgram`/`VerifiedRoutine` field carries an existential liveness proof. This is untracked backlog, not yet assigned a task ID (found by `scripts/check_doc_facade.py`, TC21, while validating that linter against this document); it is the standard new whole-program contracts are reviewed against, not a description of current enforcement.
   - *Trace Isomorphism:* Open extensible events (`Inject DomainEvent GlobalEvent`) must be identical between specification and machine traces (`specTrace == machTrace`).
   - *Code Generation Gating:* Binaries can only be produced via `emitVerifiedExecutable` consuming a proved `VerifiedProgram`.
2. **Traceability Indexing:** `python scripts/check_refs.py` must return exit code 0, AND `lake exe check_refs_coverage` -- **run from the repository root, after a build; building it is not running it, the same distinction item 4 draws for `check_gates_axioms`** -- must also return exit 0. Together these give: every `REF:` citation whose target is a `docs/` path gets full anchor-existence validation against that file's real on-disk headings, zero exceptions (`check_refs.py`); every `REF:` citation whose target is a `references.json` slug is validated for slug EXISTENCE by `check_refs.py`, with full anchor-level correctness delegated to item 3's `check_references.py --offline` (Law 6); and every reportable Lean declaration -- enumerated from the COMPILED ENVIRONMENT, so no declaration syntax form can be invisible to it -- has at least one preceding `REF:` citation, either directly or via an honest `scripts/ref_allowlist.txt` entry (`check_refs_coverage`). See §4.1.2 for why declaration coverage and citation validity are two independent tools rather than one script doing both jobs, and for the concrete history of why "100% citation validity, zero un-cited declarations" was previously an inflated claim: a regex-based single-script design could not see roughly a tenth of the codebase's own declarations (every anonymous `instance`, every `abbrev`, the one `initialize`) and silently dropped whatever citation preceded them along with it.
3. **Reference Integrity:** `python scripts/check_references.py --offline` must pass (registered slug, cache-hash-verified, anchor-resolved -- see Law 6). `python scripts/check_publishable.py` must also pass (zero third-party prose in the tree, zero dangling citations into the deleted `references/` tree, zero machine-specific paths).
4. **Gate Policy Compliance (Law 10):** `python scripts/check_gates.py` (fast source-level pre-check) must exit 0, AND `lake exe check_gates_axioms` — **run from the repository root; building the executable is not running it** — must exit 0. The axiom tool is the load-bearing gate: it walks every declaration in its import closure's kernel-recorded axiom dependencies (the closure is the `Gasm`/`Stdlib`/`Spikes` umbrella roots — see `TCB.md` T2 for the current 32-module blind spot outside that closure, including every `Spikes/*/Emit.lean`; closure-coverage completion is tracked as TC15), and any declaration it does inspect that depends on a native-evaluation axiom (`*._native.*` / `ofReduceBool` / `ofReduceNat`) — or on any axiom outside `{propext, Classical.choice, Quot.sound}`, including `sorryAx` and hand-declared axioms (this is the mechanical enforcement of item 1's zero-sorry/zero-axiom requirement — note that item 1's "zero `sorry`" is enforced HERE, not by `lake build` itself: `lakefile.toml` sets no `warningAsError`, so a stray `sorry` is only a compiler warning and `lake build` exits 0 regardless; this axiom tool, which sees `sorryAx` in the compiled environment, is what actually turns that into a hard failure) — must be allowlisted in `scripts/gate_allowlist.txt` under an honest category. See §4.1.1 below for the full gate-tooling specification. Connection-theorem coverage per Law 12 (linter: backlog).
5. **Apache-2.0 Header Compliance:** `python scripts/check_licenses.py` must return exit code 0. Every first-party file (`Gasm/**/*.lean`, `Stdlib/**/*.lean`, `Spikes/**/*.lean`, `Tools/**/*.lean`, root `*.lean`, `scripts/*.py`, `scripts/*.ps1`, `scripts/*.sh`, `lakefile.toml`, `.github/**/*.yml`, `.github/**/*.yaml`, `.github/CODEOWNERS` — the last three added when CI was established, see `docs/CI.md`) must carry the standard Apache-2.0 short-form header in its type's comment syntax; `references/` (third-party vendored material) is explicitly and visibly excluded, and the excluded count is reported on every run. Genuine exceptions require a justified entry in `scripts/license_allowlist.txt` (5 `::`-delimited fields, same shape as `scripts/gate_allowlist.txt`); stale or unjustified entries are a hard failure, same as a missing header.
6. **Decision-Record Integrity (D23/[`0035`](adr/0035-decision-record-integrity-gate.md)):** `python scripts/check_record.py` must return exit code 0. Once the flatten (D23) makes `PLAN.md`, `docs/adr/`, and `docs/tasks/` the sole surviving decision history, this record must be as mechanically checked as the code: every `D`-numbered decision in `PLAN.md` has a unique ID and either a dedicated ADR or a recorded reason it does not; every ADR carries a `## Provenance` section or a recorded reason it does not; every cross-reference (markdown link or backtick-quoted file path) inside `PLAN.md`, `docs/adr/*.md`, `docs/tasks/*.md`, `TCB.md`, `MODEL_DEBT.md`, and this document resolves to a real file on disk; and a "full inventory"/"complete list"-shaped claim is paired with a nearby verifying-check citation or a recorded reason it is trusted without one. Genuine exceptions require a justified entry in `scripts/decision_record_allowlist.txt` (5 `::`-delimited fields, same shape as `scripts/gate_allowlist.txt`) — duplicate IDs are never allowlistable. See `scripts/check_record.py`'s own module docstring for the full specification.

### 4.1.1 Gate Tooling Specification

This subsection specifies what the two Law 10 gate tools implement, so that Pillar 1's "gate policy compliance" line is a citable specification rather than an unexamined rubber stamp.

- **The allowlist file format** (`scripts/gate_allowlist.txt`): one entry per line, five `::`-delimited fields — `file::decl::fqn::category::justification`. `file` and `decl` are the bare source-text location the Python pre-check matches against (relative path and unqualified declaration name); `fqn` is the fully-qualified name exactly as Lean's environment prints it, which is what the axiom-level Lean tool matches against; `category` is one of the three below; `justification` is free text and must be non-empty. A line with any other field count, an unknown category, an empty `fqn`, or an empty `justification` is a hard parse failure for both tools — never a silently-skipped line.
- **The three categories**:
  - `finite-forall` — the occurrence discharges a proposition universally quantified over its entire finite domain (Law 10's admissible case). Permanent, not migration debt. The Python pre-check additionally requires a shallow syntactic corroboration signal (an explicit `∀`, a `for .. in [a:b]` range, a `List.range N>1`, or a non-literal `.all`/`.any`) between the declaration header and the occurrence — a sanity check, not a proof.
  - `grandfathered` — a single-vector/pointwise check that predates Law 10 and remains migration backlog (tracked in `TASKS.md`'s PA-track). Reported every run, never hidden, never silently exempted from the count.
  - `axiom-only` — an entry that exists purely for the axiom-level Lean tool: a declaration that transitively depends on a native-evaluation axiom via citing another declaration (e.g. through `VerifiedProgram` wiring), with no `native_decide`-shaped source text of its own for the Python pre-check to ever find. Exempt from the Python tool's stale-entry check by construction; the Lean tool independently fails if an `axiom-only` entry matches nothing in a scan (stale pre-authorization).
- **The standard-axiom set**: `{propext, Classical.choice, Quot.sound}` — the only axioms Lean's kernel trusts as part of ordinary, sorry-free, native-eval-free mathematics. Any declaration depending on any axiom outside this set (a native-evaluation axiom, `sorryAx`, or a hand-declared `axiom`) must carry a matching allowlist entry; this is what makes the axiom tool the mechanical enforcement of Pillar 1 item 1's zero-sorry/zero-unauthorized-axiom requirement, which had no enforcement anywhere before this tool existed.
- **Module-based scoping**: a declaration is in scope for the axiom tool if it was *compiled from* a project module (`env.getModuleIdxFor?` names a module under the `Gasm`/`Stdlib`/`Spikes` umbrella roots) — not if its own name merely looks like it lives under one of those namespaces. This closure-based scoping is itself incomplete: `TCB.md` T2 documents that 32 of 170 project `.lean` modules (every `Spikes/*/Emit.lean`, every `Test.lean`, the fuzzer CLIs, `NASM.lean`, `RoundtripTests.lean`) sit outside the tool's own import closure and are therefore invisible to it today; closing that gap is TC15.
- **Why the axiom tool keys on fully-qualified name, not bare name**: the Python pre-check can only see unqualified source text, so it keys on `(file, decl)`. The axiom tool sees the compiled environment and keys on `fqn` instead, because a bare-name key is exploitable — `namespace Foo.Bar; theorem crc32_empty : ... := by native_decide` would collide with an unrelated, already-allowlisted `crc32_empty` and pass for free. FQN-keying is what closes that collision.
- **The two-tool split**: `scripts/check_gates.py` is a fast, milliseconds-scale, line-regex pre-check over `.lean` source text — defense-in-depth, not the gate, because it can only recognize tactic spellings it already knows and cannot see what the compiled kernel environment actually recorded. `lake exe check_gates_axioms` (`Tools/CheckGatesAxioms.lean`) is the load-bearing gate: it imports the project and asks Lean's own axiom-dependency machinery (`Lean.collectAxioms`) which axioms each declaration depends on, which is immune to source-level disguise because it reads what the kernel recorded rather than what the source text says. Neither tool's coverage alone is authoritative; today the two tools' union is what is actually checked (see TC15 for closing that gap for the axiom tool specifically).
7. **Doc-Facade Linter (TC21):** `python scripts/check_doc_facade.py` must return exit code 0. Detects normative docs (`docs/*.md`, excluding `docs/adr/` and `docs/tasks/`) asserting enforcement the tree does not actually provide: a backtick-quoted Lean identifier cited inside a MUST/is-implemented-shaped claim that does not appear anywhere in the `.lean` tree (`MECHANISM_ABSENT`), or this document naming a script/`lake exe` target as a required gate that either does not exist on disk or exists but is not wired into `scripts/run_gates.py`'s gate table (`GATE_SCRIPT_MISSING`/`GATE_NOT_WIRED` — the shape that let `check_licenses.py` go unwired despite being listed as required, discovered this week). Honors the `**Status**:` escape hatch (Law 9): a claim honestly marked designed-not-built is never flagged. Genuine exceptions require a justified entry in `scripts/doc_facade_allowlist.txt` (5 `::`-delimited fields, same shape as `scripts/gate_allowlist.txt`). See `scripts/check_doc_facade.py`'s own module docstring for the full specification, including the shapes deliberately rejected as unable to be made precise.
8. **Differential Fuzzers (PR-scoped):** `lake exe test_roundtrip`, `lake exe x86_fuzzer` (hardware oracle), `lake exe encoding_fuzzer` (NASM oracle), `lake exe wasm_fuzzer` (node oracle), and `lake exe gzip_fuzzer` (python stdlib oracle) must all exit 0.
9. **Spike/Stdlib CLI test suites:** the spike and stdlib `test_*` executables that `defaultTargets` builds — `lake build` compiling them is not the same as running them (the same distinction item 4 draws for `check_gates_axioms`) — must also be invoked and must exit 0. See `scripts/run_gates.py`'s gate table for the current list.

### 4.1.2 Reference Coverage Tooling Specification

This subsection specifies what the two Law 1/Law 3 citation tools implement, analogous to §4.1.1's specification for Law 10. It exists because `scripts/check_refs.py`'s original single-script design had a vacuous-gate defect: it detected un-cited Lean declarations (Law 1) with a regex, `LEAN_DECL_REGEX`, that REQUIRED an identifier immediately after the declaration keyword — structurally blind to an anonymous `instance : Foo X where` (no name token at all), and missing `abbrev`/`initialize` from its keyword list entirely. The consequence was worse than a missed warning: because the same script's citation-collection loop only kept a pending `REF:` comment around until it matched a recognized declaration, a `REF:` comment sitting directly above one of these invisible declarations was silently DROPPED — never validated at all, not merely unvalidated-but-flagged. At least 22 Intel `#operation` citations on anonymous `instance` declarations, plus Wasm declarations, were affected before this was found and fixed.

- **The fix is two independent mechanisms, not one script doing two jobs**:
  - **Citation validity** (does a `REF:` target resolve to a real section or registry entry) needs no Lean parsing whatsoever. `scripts/check_refs.py`'s `collect_ref_citations` scans every line of every `.lean` file for a `REF:`-shaped regex match and validates each target, full stop — it is not coupled to "the declaration that follows" in any way, so no declaration form can make a citation invisible to it.
  - **Declaration coverage** (does every declaration have a preceding `REF:`) is driven entirely by the COMPILED ENVIRONMENT rather than source text. `lake exe check_refs_coverage` (`Tools/CheckRefsCoverage.lean`) walks every declaration Lean's own elaborator actually produced, so no syntactic declaration form — `abbrev`, anonymous `instance`, `initialize`, or any future keyword — can hide from it the way one hid from a regex.
- **Bridging declaration name to source position**: the environment records declaration NAMES, not source positions, while a `REF:` citation is a source-level concept (physically precedes a declaration). `Tools/CheckRefsCoverage.lean` bridges this with `Lean.findDeclarationRanges?`, confirmed empirically (against Lean toolchain v4.33.1) to return real, file-accurate positions for every directly-authored declaration in a plain (non-`module`-system) project file via an ordinary `importModules` call — no special `OLeanLevel`, no `.olean.server` artifact required. `selectionRange.pos.line` (always the declaration keyword/name's own line) is the anchor a block-comment-aware upward text scan starts from — the same scan `scripts/check_refs.py`'s citation collector always used, just triggered by a real declaration position instead of a regex match.
- **Filtering out compiler-synthesized declarations**: the raw environment surfaces far more than a human wrote — structure field projections, `rec`/`recOn`/`casesOn`/`noConfusion`, `deriving`-clause instances, equational/injectivity byproducts. None of these are independently "invented" content Law 1 could sensibly demand a citation for. `Tools/CheckRefsCoverage.lean` excludes them via real Lean APIs (`Environment.isProjectionFn`, `Lean.isAuxRecursor`, `Lean.isNoConfusion`, `ConstantInfo` kind exclusion for `.ctorInfo`/`.recInfo`/`.quotInfo`, and "no declaration range at all") plus one general-purpose structural check: a candidate declaration whose range is wholly CONTAINED within a different candidate's range in the same module is a byproduct of the enclosing declaration (this is what catches `deriving`-generated instances specifically, confirmed empirically to always be nested inside their structure's own range) — see that file's own header comment for the full empirical basis of each exclusion.
- **The allowlist file format** (`scripts/ref_allowlist.txt`): same 5-field `::`-delimited shape as `scripts/gate_allowlist.txt` — `file::decl::fqn::category::justification`, matched by `Tools/CheckRefsCoverage.lean` on `(module derived from file, fqn)`, same module-qualified-keying rationale as the axiom gate's allowlist (a bare fqn is not unique project-wide). Categories: `derived-scaffolding` (a declaration independently visible to the environment scan that is still mechanical scaffolding around an already-cited declaration), `internal-helper` (a small, self-evidently trivial declaration with no citable concept of its own), `grandfathered` (predates this tool's mechanical enforcement, tracked migration backlog). A malformed line, unknown category, empty `fqn`, or empty justification is a hard parse failure, same discipline as every other allowlist in this repository.
- **Module-based scoping and the TC15-style closure fix**: identical in structure to the axiom gate's (§4.1.1) — `Tools/CheckRefsCoverage.lean` reuses the same `discoverProjectModules` (disk-walk, independent of any import closure) plus baseline-import-then-standalone-per-module-import technique `Tools/CheckGatesAxioms.lean` uses to close the "32 modules outside the Gasm/Stdlib/Spikes umbrella's own import graph" gap, so declaration coverage does not inherit that blind spot either. `Tools/` is excluded from scope, matching `isProjectModule`'s existing Gasm/Stdlib/Spikes-only namespace scope.

**Standard invocation:** `python scripts/run_gates.py` is the single entry point that runs every gate above (in the fixed order documented in the script's own docstring, which is not required to match this list's item numbering), capturing each process's exit code directly (never through a pipe/tee — see the tool's own docstring for the Merge-Train-2 incident this closes). In its default (full) mode it is fail-closed on missing oracle prerequisites (NASM, node): a missing prerequisite **aborts the entire run** (distinct exit code 3) rather than silently skipping the gate that needs it, and it records every oracle's detected version (node/python/NASM banners, `lean --version` vs. the `lean-toolchain` pin) in its output. `--quick` skips the slow differential fuzzers for local iteration only, reports a distinct `PASSED_PARTIAL` status (never the same `PASSED` a full run reports) and a distinct exit code, marks every skipped gate explicitly (`SKIPPED (--quick)`, in both the table and the JSON `mode`/`gates` fields — never simply absent), and **still performs prerequisite detection for every gate in the full list, waiving only the ones it actually skipped** — it is **not sufficient evidence for merge sign-off** under any circumstance. `--clean` runs `lake clean` first (merge-train mode); `--json` emits a machine-parseable summary for CI (TC6), always including a `mode` field so `PASSED`/`0` cannot be produced by anything other than a genuine full run of every gate in this section. Gate 1 above is satisfied, at minimum, by a full-mode (`python scripts/run_gates.py`, no `--quick`) run exiting 0; item 9's spike/stdlib suite coverage is tracked for completeness in `scripts/run_gates.py`'s own gate table rather than duplicated here.

### 4.2 Pillar 2: Semantic Integrity & Adversarial Domain Gap Hunting
If CI passes, the reviewer operates as an adversarial semantic auditor. Reviewers MUST append the following structured sections to their review artifact for every formal theorem under review:

#### A. Structured Spec-to-Theorem Derivation
1. **Spec Requirement:** Quote the exact domain contract $P(x)$ and preconditions $Q(x)$ from the cited `docs/` section.
2. **Formal Theorem:** Paste the exact Lean signature $\forall x, H_1(x) \land \dots \land H_k(x) \implies C(x)$.
3. **Fidelity Mapping:** Step-by-step mathematical justification proving bijectivity:
   - $H_i \iff Q$ (The formal preconditions are not artificially stricter than the specification).
   - $C \iff P$ (The formal conclusion guarantees the exact state transitions and observable effects mandated by the spec).

#### B. Adversarial Domain Gap Hunting
Reviewers MUST actively search for valid input configurations, edge conditions, boundary states, error paths, or behaviors that the **written specification allows/mandates**, but that the **formal theorem accidentally excludes, weakens, or ignores**.

Reviewers MUST include a **Domain Gap Matrix**:

| Spec Permitted Behavior / Input Space | Theorem Hypothesis / Bound | Gap Status (`Verified` / `Weakened` / `Uncovered`) | Justification & Impact |
| :--- | :--- | :--- | :--- |

### 4.3 Pillar 3: Structured Architectural Health Audit
Reviewers MUST author an explicit evaluation across four architectural axes:
1. **Target Separation & Placement:** Does all code live in its correct domain hierarchy (`Core/`, `Effects/`, `Targets/`, `Stdlib/`) without bleeding OS or hardware concepts across abstraction boundaries?
2. **Abstraction Cleanliness:** Are typeclasses decoupled, and are event types open and extensible via `Inject`?
3. **Factoring & DRY:** Is common execution, decoding, or emission infrastructure factored into shared modules rather than duplicated across spikes or libraries?
4. **Diffusion vs. Concentration:** Are critical system invariants centralized in authoritative modules rather than scattered across disparate files?

### 4.4 The Approval State Machine
- **Gate 1 (Mechanical):** Did `python scripts/run_gates.py` (full mode; see Section 4.1) — `lake build`, `python scripts/check_refs.py`, `python scripts/check_gates.py`, `lake exe check_gates_axioms` from the repo root, `python scripts/check_references.py --offline`, `python scripts/check_publishable.py`, `python scripts/check_licenses.py`, `python scripts/check_record.py`, `python scripts/check_doc_facade.py`, the differential fuzzers, and the spike/stdlib CLI test suites — pass?
  - *No $\to$ REJECT IMMEDIATELY.*
- **Gate 2 (Semantic):** Was the Spec-to-Theorem Derivation provided? Are there any `Weakened` or `Uncovered` domain gaps in the matrix?
  - *No / Yes $\to$ REJECT.*
- **Gate 3 (Architectural):** Was the four-axis structured architectural audit provided? Does it flag any boundary leakage, duplication, or invariant diffusion?
  - *No / Yes $\to$ REJECT.*

If and only if all three gates evaluate to TRUE, the reviewer MUST approve.
