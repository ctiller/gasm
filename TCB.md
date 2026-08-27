# TCB LEDGER — gasm trusted computing base

> Inventory of everything trusted but not proven (assumptions, where MODEL_DEBT.md is
> omissions). Policy (D13/ADR-0013): every trust item we cannot prove gets a
> differential validator; where an item is *shrinkable*, proof beats fuzzer (Law 13
> preference order — trust⇒fuzzer is the floor, not the ceiling). Opus audit
> 2026-08-27 @ 1cf58d5; line numbers from that tree. Feeds docs/tasks/ (TC7→TC8+).

**Headline metrics.** 171 project `.lean` modules (170 excluding `Tools/`); **138 reachable from umbrella roots, 32 not**. 92 theorems tree-wide; **zero theorems across the 1,255 lines of `Gasm/Targets/Windows/*.lean` + `Wasm/{Linker,Binary}.lean`**. Allowlist: 55 entries (36 grandfathered / 13 axiom-only / 6 finite-forall) — grown by 1 (`trapShortCircuitGuard_inst`) since the 54-native-dependent count in T1 below was taken; both numbers are correct for their respective snapshots. `references/`: 1,048 files, zero hashes. No CI; every gate manual.

---

## T1 — Lean kernel, Lake, toolchain pin — IRREDUCIBLE
Trusted: v4.33.1 toolchain, Lake, C backend for the 54 native-dependent declarations
(count at audit time, commit `1cf58d5`; the allowlist has since grown to 55 entries —
see headline metrics above — after a merge added `trapShortCircuitGuard_inst`. Both
numbers are correct for their respective snapshots; this ledger has not re-run the
axiom scan to confirm whether the new entry moved the native-dependent count itself). `lake-manifest.json` has `"fixedToolchain": false` — nothing fails if pin and installed toolchain diverge. No external Lean deps (TCB is Lean core alone). Proposed: gate runner asserts `lean --version` == pin and records it; a toolchain bump re-runs the full differential suite BEFORE the pin moves — `CheckGatesAxioms`'s axiom-name detection is empirically toolchain-specific and an upgrade can silently blind the gate. Priority: low-med. Shrink: kernel no; the native_decide surface yes (migrate 36 grandfathered entries).

## T2 — Axiom gate sees only 81% of the tree — HIGHEST-VALUE SHRINK (~20 lines)
`isProjectModule` (`Tools/CheckGatesAxioms.lean:94-101`) sees only the tool's import closure (Gasm∪Stdlib∪Spikes roots): **32/170 modules invisible — every `Spikes/*/Emit.lean`, every `Test.lean`, all four fuzzer CLIs, NASM.lean, RoundtripTests.lean**. A `sorry`/`axiom`/unallowlisted `native_decide` in the emission path passes the load-bearing gate. (The demoted python scanner globs all 170 — neither tool dominates; the real gate is their undocumented union.) Fix: enumerate `.lean` files from disk inside the tool; fail if any lacks a module in `env.allImportedModuleNames`. Control vector: scratch unimported module with `sorry` ⇒ red. Priority: **1 (tie)**. Fully shrinkable.

## T3 — Elaboration-time metaprograms
One real `run_cmd`: `Registry.lean:95-142` (instance audit + non-emptiness floors). Census otherwise clean: zero `@[extern]`/`@[implemented_by]`/`unsafe`/`sorry`/user-`axiom`/custom macros. Gaps: unimported Instructions file invisible (self-documented `Registry.lean:6-15`); aggregate floor (`:139`) lets one family shrink 200→1; `familyCounts` (`:124-133`) hand-maintained, new family exempt; `run_cmd` structurally exempt from check_refs (decl-regex can't see it) — the most trusted metaprogram cannot carry a REF. Fix: fold filesystem-vs-closure check into T2's harness; derive familyCounts from the manifest. Priority: 4. Shrinkable.

## T4 — Gate tooling + no runner
Tools themselves hardened (fail-closed parsing, stale/dup detection). Outage is one level up: **nothing runs them** — `defaultTargets` *builds* check_gates_axioms; REVIEW.md itself warns building ≠ running. Soft spots: `check_refs.py:35-47` slugifier has no duplicate-heading disambiguation (a REF to the second identically-titled section silently resolves to the first — Law 2 satisfied against the wrong section); Law 10 is 11% enforced / 65% grandfathered. Fix: TC5 runner + a **meta-gate** fixture (planted sorry / unallowlisted native_decide / broken REF / duplicate heading — each gate must go red). Priority: **2 (tie)**. Shrinkable.

## T5 — THE EMITTER LAST MILE — LARGEST ITEM
Everything past `serializeInstructions` (`Assembler.lean:349-350`): 1,255 lines, zero theorems. Structural gap: **`VerifiedProgram` (`Core/Verification.lean:64-72`) carries `executable` and `instructions` as INDEPENDENT fields — no proposition links `executable.textBytes` to `serializeInstructions instructions`;** `traceEquivalence` walks the list, `emit` writes the bytes, and nothing the proof observes reads them. A VerifiedProgram with proven instructions and arbitrary bytes typechecks. Latent hazards found: `entryRva`/`imageBase` honored by `load`, ignored by `emit` (`Emitter.lean:196`); `computeSectionLayout` called with three different `idataSize` values (coincidentally safe); linker lays out from `estimatedSize` while emit/load use encoded size (no mechanical link); symbol resolution `.getD curRip` at 21 sites — a mistyped import assembles a jump-to-self silently; `dllCharacteristics` spec/emit disagree (0x8160 vs 0x8120); `imageBase` in three unlinked copies; `isValidEntryState` has zero call sites. Validation today: three spike exes running; **Spike 4 and Spike 5 Windows PEs are written and never executed**. Proposed: (i) byte-level PE parser in Lean + `parse (emit exe) = exe` connection theorem + new `VerifiedProgram.codeMatches` field (class unrepresentable — Law 13 pref 1); (ii) structural differential vs dumpbin/pefile on every emitted binary (corrupted-header control vectors); (iii) loader-behavior harness — run EVERY spike PE. Priority: **1 (tie)**. Shrinkable — highest-yield shrink in the repo.

## T6 — IAT/loader convention — KNOWN divergence (MODEL_DEBT C6)
`findIatIndex` keys on a slot containing its own address — a convention `loadMemory` manufactures; **the real loader writes the resolved VA.** 4KB-boundary assumption; positional dispatch skipping index 6 (per-DLL null terminator, stride reimplemented ×3); `| _ => none` fail-open default. Every trace proof is conditioned on a false premise about the OS; binaries work because interception never happens in reality. Fix: Win32 differential harness dumps the real post-load IAT and diffs vs synthesized; re-key interception on resolved VA. Priority: 3. Shrinkable (replace invention with measurement).

## T7 — Wasm binary emission
`Wasm/Linker.lean` + `LEB128.lean` unproven; **no LEB128 decoder exists** (roundtrip unstatable); `encodeI64SLEB128 := encodeI32SLEB128` (no width bound); section order enforced by comments; `findTypeIdx` returns 0 on not-found (type mismatch silently encodes as index 0). V8 validates fuzzer-synthesized modules only — never spike modules. Fix: write the decoder (missing half of a Law 12 connection theorem), prove LEB128 roundtrip, `wasm-tools validate`/`WebAssembly.validate` over every emitted spike module (byte-flip control vector). Priority: 5. Shrinkable.

## T8 — References pipeline — Law 4's ground truth passes through regex

> Live demonstration (2026-08-27, found during docs/tasks G-track authoring):
> `spirv.core.grammar.json` is named in regenerate_references.py's manifest and was
> cited by GRAPHICS_PREBUILD_AUDIT.md as ingested — **the file does not exist on
> disk** (references/spirv/ holds only four prose chapters). `--verify` passes anyway.
> Manifest-membership ≠ disk-presence is exactly the class this entry describes.
> RESOLVED by TC16 (958de07, in review): root cause was `regenerate_spirv()` fetching
> the JSON into memory to build INDEX.md and never writing the file. Now written
> (632,922 bytes, 877 instructions) and hash-pinned.
>
> **NEW LAW 4 EXPOSURE found by TC16 — self-authored "reference" material.** Law 4:
> *"We do NOT author or synthesize ad-hoc approximations of hardware manuals or external
> OS specifications; that is a massive cheat."* But `references/` contains files with no
> fetch source at all: `references/windows/{readfile.md, winsock2.md}` and
> `references/wasm/{binary,execution,structure,text}.md` are hand-authored, and the
> entire `references/vulkan/` corpus (72 files) was never fetched — same unreproducible-
> vendored-blob class as intel_sdm (928 files). TC16 disclosed all of it honestly in
> MANIFEST.provenance.json rather than counting them as fetched. Consequence: every
> `REF:` citation into those files cites text this project wrote about someone else's
> spec — the exact cheat Law 4 names. Remediation is a new task (fetch paths where
> upstreams exist; itemized "vendored blob" declarations where they don't; and an
> honest audit of which Lean declarations currently derive from self-authored text).
> CONFIRMED INDEPENDENTLY (N1 design review, same day): `references/windows/readfile.md`
> is 28 lines with **no `source_url`, no frontmatter, and no Remarks section at all** —
> opening instead with "Official Microsoft Reference: Windows SDK fileapi.h / MSDN
> Library". The Remarks section is exactly where every fact the Win32 read model needs
> lives (when ReadFile returns on a pipe; TRUE with zero bytes at EOF; ERROR_BROKEN_PIPE
> when write handles close). By contrast `writefile.md` (584 lines, `source_url`, full
> Remarks) is genuinely vendored — so the corpus mixes real and synthesized material with
> nothing distinguishing them. Consequence per VISION §3.2: a model surface with no
> vendored contract behind it has no ∀-source at all, so N1's harness was designed to
> validate a read model against text this project wrote about someone else's spec.
> Law 4 ingestion of the Win32 surface is now a BLOCKING prerequisite to N2.
`verify_references()` checks directory-exists + file_count≠0 — **passes on a corpus truncated to one byte per file**. No hashes, no manifest, no fetch dates. Regex conversion strips all tags (**silently flattening every table** — how SDM opcode tables arrive); 5-entity decode chain; `errors="replace"` substitutes U+FFFD instead of failing; `<main>` extractor falls back to whole document. Six of eight corpora track moving refs. **intel_sdm = 89% of corpus, no URL, unreproducible; missing-corpus path is a print, not a raise.** A declared Pillar-1 gate that does not exist. Fix: per-file SHA-256 manifest; `--verify` fails nonzero on mismatch; size floors; commit-SHA pinning; converter fixture suite as control vectors; SDM gets a genuine ingestion path or an honest "vendored blob, unreproducible" declaration. Priority: **2 (tie)**. Shrinkable to a hash check.

## T9 — Oracle environment — unpinned
node/python/nasm/powershell/OS: no version recorded or asserted anywhere; `NASM.lean:41-48` fetches `nasm -v` and **discards the banner**. Silent drift undetectable. Fix (TC5): capture + print all oracle versions in gate output; pin floor/ceiling; commit the version tuple with recorded fuzz results. Priority: 3 (tie). Not shrinkable (world is the oracle) but fully recordable.

## T10 — HardwareHarness's hand-written machine code
~600 bytes across **94 raw `ByteArray.mk` literals** — the oracle validating the encoder is not built by the encoder (`mov r64,imm64` hand-written at 14 sites while `mov_r64_imm64` exists). `setupSize := 46` manually asserted, nothing checks it. `HardwareHarness.lean:270` calls `emitPE32Executable` directly — live counterexample to "binaries only via emitVerifiedExecutable". Fail-closed structure + controls are real and reference-grade; residual: `Inhabited HardwareExecutionResult` fabricates `faulted := false` (contradicts the no-fabricating-path docstring; reachable via `getD`), and `getU8` returns 0 out-of-range so an untouched zero buffer decodes plausibly — only the positive control catches it. Fix: **self-host** — rebuild prologue/capture/epilogue from `X86_64Instruction.encode` via the registry (the hand-vs-generated diff is itself the one-time control vector); delete the Inhabited fabricator; derive setupSize. Priority: 4 (tie). Clearest self-hosting win; converts 94 unlinked twins into a proof obligation.

## T11 — The silicon itself
One i9-13900H is the sole truth source; ~half the ISA `canFuzzHardware := false` (unvalidated SDM transcription); skylake/zen4 profiles unvalidatable by construction. **T11-b vacuity (cheap, priority 2):** zero-state instructions record `passed := true, totalTested := 0`; flipping every canFuzzHardware to false yields "0 fuzzed, 0 failed, exit 0"; same shape in Wasm fuzzer; **`PerfFuzzerCLI --count 0` prints "100% SUCCESS" with no oracle at all.** Fix: vacuity floors (nonzero vectors or hard fail) + "validated on exactly N microarchitectures" disclosure in gate output. Multi-silicon: priority 6 (Linux hardware plan, B2). Not shrinkable; coverage expandable.

## T12 — Verification harness layer
(i) **Fuel exhaustion indistinguishable from clean termination**: `runProgramTraceWithLoops` returns `[]` for fuel-out, no-instruction-at-rip, and clean fault alike — any spec expecting `[]` is dischargeable by fuel exhaustion. Soundness gap in the contract. (ii) **`Environment` entirely dead** — no VerifiedProgram instantiates it (Spike3 uses `Env := Bool`); its docstring claims to model all syscall-queryable data. Law 8 facade. (iii) `rawEmitForFuzzing`: zero call sites — dead code standing as a permanently open bypass (real bypass is HardwareHarness.lean:270). Fix: trace type `Except Exhausted (List Event)`; delete rawEmitForFuzzing; instantiate or delete Environment. Priority: 3. Fully shrinkable — deletions and type changes.

## T13 — Git, build cache, result persistence
3.1 GB `.lake/build` caches elaboration-time audit passes (a stale artifact replays a pass without re-running). Fix: gate runner does one clean-tree build before merge-train sign-off (mechanize D6). Adjacent: zero recorded calibration/golden/regression data in git — no divergence can become a permanent vector (TC10). Priority: 7. Mechanizable.

---

## RANKED TOP 8

| # | Item | Why |
|---|---|---|
| 1 | T5 emitter last mile | 1,255 lines / 0 theorems; VerifiedProgram never links bytes to instructions; 2 of 5 PEs never executed |
| 2 | T2 axiom-gate blind spot | Load-bearing gate misses 32/170 modules incl. every Emit.lean; ~20 lines |
| 3 | T8 references verify facade | Declared Pillar-1 gate that only counts files; 89% of corpus unreproducible |
| 4 | T4 no gate runner / no CI | Everything manual; built ≠ run; blocks TC6/TC10/TC11 |
| 5 | T11-b vacuity floors | `--count 0` ⇒ "100% SUCCESS"; zero-vector auto-PASS constructible |
| 6 | T6 IAT convention | Known model-vs-OS divergence, not suspected |
| 7 | T10 harness self-hosting | 94 unlinked twins; encoder's oracle not built by encoder; Inhabited fabricator live |
| 8 | T12 verification harness layer | Fuel exhaustion indistinguishable from clean termination; `Environment` entirely dead (vacuous ∀); dead `rawEmitForFuzzing` bypass |

*T9 (oracle version pinning) folds into TC5 — it is one of TC5's gate-runner deliverables (capture + print oracle versions), not deprioritized; dropped from this ranked-8 table to make room for T12 rather than pushing the table to 9 rows.*

One-line fixes to fold into TC5/TC9: EncodingFuzzer has NO control vectors (only oracle with zero Law 13(4) compliance); Spike1/2 Wasm Test.lean print "100% sound" and return 0 when no runner exists; GzipFuzzer.lean:84 reads binary .gz as UTF-8 lines, destroying its own diagnostic.

## Irreducible vs shrinkable
**Irreducible:** Lean kernel (T1); silicon (T11); V8/CPython and the real Windows loader's *actual behavior*, used as measurement ground truth (T9's oracle environments) — for these, Law 13(4) controls + recorded provenance. T6 does NOT belong in this bucket wholesale: the real loader's behavior is irreducible (it is exactly what T6's fix must measure against), but T6's own defect — the *invented IAT convention* (`findIatIndex` keying on a slot containing its own address, a fiction `loadMemory` manufactures) — is shrinkable, per T6's own entry above ("replace invention with measurement"); it is listed under Shrinkable below, not here. The Wasm fuzzer's control architecture (three controls, enforced on the callee) is the reference implementation — it exists because that harness was caught failing open twice; nothing else is built to that standard yet.
**Shrinkable (most of the ledger):** T2, T3, T4, T5, T6, T7, T10, T12, T13 are missing *code*, not accepted risk. T5 and T10 are genuine self-hosting opportunities — proof, not fuzzer: strictly better under Law 13's preference order.
