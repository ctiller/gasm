# Third-Party License Audit — `references/`

**STATUS (2026-08-27): historical record. `references/` has been deleted in its entirety** (owner
ruling: no third-party prose ships regardless of redistributability — see `docs/REVIEW.md` Law 4,
`docs/REFERENCE_INDEX.md` §7). None of the corpora this document analyzes are in the tree any
more; nothing below is a live compliance surface. Kept, not deleted, because it remains the
durable answer to "was anything non-redistributable ever in this repository" once the flatten
(`docs/REFERENCE_INDEX.md` §6.6) erases the commit history that would otherwise have shown this.

**Purpose.** `gasm` is about to be open-sourced under Apache License 2.0. `references/`
contains ~1,049 files of vendored third-party material (per-corpus counts below, cross-checked
against `references/MANIFEST.provenance.json` and `references/MANIFEST.sha256`). This document
records, per corpus (and per file where corpora are mixed), what license governs the upstream
work, whether verbatim/converted redistribution in a public Apache-2.0 repository is lawful,
what attribution the license requires, and a verdict.

## Disclaimer — read before acting on this document

**I am not a lawyer and this is not legal advice.** This is a researched, cited factual survey:
license text and terms-of-use text as published by each upstream, cross-referenced against what
is actually stored in this repository (verbatim copy vs. reformatted/machine-converted derivative,
which matters because several of these licenses treat "unmodified copy" and "derivative work" as
legally distinct categories with different — sometimes zero — permissions). Where the facts left
genuine room for interpretation I have said so and marked the item **UNCLEAR**. I have deliberately
erred toward flagging: a false "this is fine" here is far more costly than a false alarm. **Every
verdict below, and especially every item in the BLOCKERS section, needs the repository owner's
(or counsel's) own legal judgment before the project is made public.** Nothing in this document
should be read as a representation that Anthropic or the author has cleared these files for
publication.

---

## 1. Per-corpus verdict table

| Corpus | File count | Upstream work | License (spec/prose text) | Source | Verdict |
|---|---|---|---|---|---|
| `intel_sdm/` | 928 | Intel® 64 and IA-32 SDM | Intel proprietary manual license — unmodified-copy only, **no derivatives** | none recorded (unreproducible) | **NOT REDISTRIBUTABLE** |
| `vulkan/` | 72 | Vulkan® 1.3-Extensions Specification | Khronos Specification Copyright License — unmodified-copy only, **no derivatives** | never fetched (unreproducible) | **NOT REDISTRIBUTABLE** |
| `spirv/` ch_01–ch_04 + INDEX.md prose | 5 | SPIR-V Unified Specification | Khronos Specification Copyright License — unmodified-copy only, **no derivatives** | registry.khronos.org (conversion tool lost) | **NOT REDISTRIBUTABLE** |
| `spirv/spirv.core.grammar.json` | 1 | SPIRV-Headers repo | Khronos permissive header license (MIT-style; see §3) | KhronosGroup/SPIRV-Headers, commit `4965431` | REDISTRIBUTABLE-WITH-ATTRIBUTION |
| `wasm/{syntax,binary,text,exec,valid}/*.md` | 19 | W3C WebAssembly Core Specification | W3C Document License | webassembly.github.io/spec | REDISTRIBUTABLE-WITH-ATTRIBUTION* |
| `wasm/{binary,execution,structure,text}.md` | 4 | **none — hand-authored by this project** | N/A (we own the copyright) | N/A | Not a license issue — see §5 caveat |
| `wasm/INDEX.md` | 1 | generated index | N/A | N/A | Not third-party |
| `wasi/preview1.md` (docs.md) | 1 | WASI Specification | W3C Community Final Specification Agreement | WebAssembly/WASI, commit `a206794` | REDISTRIBUTABLE-WITH-ATTRIBUTION |
| `wasi/api.md` | 1 | wasi-libc `api.h` | Apache-2.0 / Apache-2.0-with-LLVM-exception / MIT (repo tri-license) | WebAssembly/wasi-libc, commit `6036a9f` | REDISTRIBUTABLE-WITH-ATTRIBUTION |
| `wasi/INDEX.md` | 1 | generated index | N/A | N/A | Not third-party |
| `zlib/RFC1950.md, RFC1951.md, RFC1952.md` | 3 | IETF RFCs (1996) | Original per-document 1996 notice (see §3) — copying/redistribution **with marked changes** permitted | rfc-editor.org | REDISTRIBUTABLE-WITH-ATTRIBUTION |
| `zlib/INDEX.md` | 1 | generated index | N/A | N/A | Not third-party |
| `png/RFC2083.md` | 1 | IETF RFC 2083 (1997) | Same 1996-style RFC notice | rfc-editor.org | REDISTRIBUTABLE-WITH-ATTRIBUTION |
| `png/lodepng.h`, `lodepng.cpp` | 2 | LodePNG (Lode Vandevenne) | zlib License | lvandeve/lodepng, commit `2256188` | REDISTRIBUTABLE-WITH-ATTRIBUTION |
| `png/stb_image.h`, `stb_image_write.h` | 2 | stb (Sean Barrett) | dual MIT / Public Domain (Unlicense) | nothings/stb | REDISTRIBUTABLE-WITH-ATTRIBUTION |
| `png/INDEX.md` | 1 | generated index | N/A | N/A | Not third-party |
| `windows/` (all 6 files) | 0 (was 6) | Microsoft Learn / MicrosoftDocs — CC-BY-4.0 for 4 files; 2 were hand-authored, no upstream | N/A — directory deleted | N/A | **DELETED.** Per the owner's no-third-party-prose ruling, `references/windows/` was removed in its entirety (not merely the 2 hand-authored files) rather than kept as a redistributable-but-legally-clear exception. All 37 `REF:` citations that pointed into it (23 into the 4 genuine files, 14 into the 2 hand-authored ones) are re-grounded onto real `learn.microsoft.com`/`MicrosoftDocs` URLs registered by slug + SHA-256 in `references.json` (`docs/REFERENCE_INDEX.md`) — see that file for the per-slug provenance this table used to carry for these files.‡ |

\* see §3 nuance on the W3C "no derivative technical specifications" clause.
† (historical) three of these four files were scraped directly from the `learn.microsoft.com` HTML rendering rather than the GitHub source; §3 explains why CC-BY-4.0 (not the generic, more restrictive Microsoft Learn Terms of Use) is nonetheless the applicable license. Kept for the record even though the files themselves are gone (see ‡).
‡ `references/windows/` predates the owner's later ruling that even legally-clearable, CC-BY-4.0, attribution-satisfiable third-party prose does not belong vendored in the repository at all — the corpus was fully redistributable (unlike `intel_sdm/`/`vulkan/`/`spirv/` prose below), which is precisely why its removal was a policy choice, not a license compliance fix. The `references.json` entries that replaced it record the same `license`/`distribution` facts this row used to (`cc-by-4.0`, `attribution-required`), just per-document instead of per-corpus.

File-count cross-check (current `references/MANIFEST.sha256`, regenerated after this edit): 928+72+6+22+3+4+6 = 1,041 across 7 corpora. `windows/` no longer appears (was 6 files); `wasm/`'s count above (24) predates a separate, already-landed fix that deleted its 2 zero-citation hand-authored files, so the live count there is 22, not 24 — this table's `wasm/` rows are otherwise unchanged by that fix and not rewritten here.

---

## 2. Corpus-by-corpus detail

### 2.1 `intel_sdm/` — 928 files, 89% of the corpus — **HIGHEST RISK**

- **No source URL is recorded anywhere** (`MANIFEST.provenance.json`: `"reproducible": false"`,
  `"known_source_urls": []`). The content cannot even be traced back to a specific Intel PDF
  edition/date from the repo alone (the on-disk `INDEX.md` states "Order Number: 325462-092US,
  Date: December 2024," which is at least a citable edition).
- **License** (confirmed against Intel's own manual boilerplate, reproduced verbatim across all
  SDM volumes, e.g. <https://cdrdv2-public.intel.com/671098/335592-sdm-vol-4.pdf>): *"No license
  (express or implied, by estoppel or otherwise) to any intellectual property rights is granted
  by this document, with the sole exception that a) you may publish an unmodified copy and b)
  code included in this document is licensed subject to the Zero-Clause BSD open source license
  (0BSD)... However, no rights are granted to create modifications or derivatives of this
  document."*
- **Why this corpus fails even the narrow exception it's given.** The one thing Intel permits —
  publishing an *unmodified* copy — is not what was stored here. The historical ingestion
  pipeline runs the SDM through a 5-entity-decode, tag-stripping regex converter that **silently
  flattens every table** (how SDM opcode/encoding tables arrive) and splits the manual into 928
  separate per-chapter Markdown files with added navigation/frontmatter. That is a derivative
  work by any ordinary reading of the term, and Intel's grant explicitly withholds permission to
  create one. The 0BSD carve-out only covers literal code listings embedded in the manual, not
  the prose/tables that make up the bulk of these 928 files.
- **Verdict: NOT REDISTRIBUTABLE** in its current (reformatted, unattributed-edition, unpinned)
  form. This is a blocker (see §4).
- **Citation impact:** 263 direct Lean `REF:` citations across 33 files, entirely within
  `Gasm/Targets/X86_64/**` (the x86-64 encoder/decoder, instruction registry, fuzzers, and
  performance model). This is the single largest citation surface into `references/` in the
  entire tree — by a wide margin.

### 2.2 `vulkan/` — 72 files — never fetched

- `MANIFEST.provenance.json`: `"reproducible": false"`, `"known_source_urls": []` —
  `regenerate_vulkan()` only checks that the files already exist; it never fetches anything.
  Every file was placed by hand or by a tool no longer in the repo.
- **License.** The task brief's assumption ("typically dual CC-BY-4.0 / Apache-2.0") does **not**
  hold for the Vulkan specification prose itself. The actual specification document
  (`vkspec.html`, mirrored at `docs.vulkan.org/spec/latest/chapters/preamble.html`) states in its
  own preamble: *"Khronos grants a conditional copyright license to use and reproduce the
  unmodified Specification for any purpose, without fee or royalty... no licenses to any patent,
  trademark or other intellectual property rights are granted."* This is the **Khronos
  Specification Copyright License** (registry.khronos.org/speccopyright.html) — an
  unmodified-copy-only license, not CC-BY-4.0. (CC-BY-4.0 does appear at Khronos, but governs a
  different artifact class — the companion *header/tooling* repos such as SPIRV-Headers, §2.3 —
  not the human-readable specification text.)
- Every file in this directory (`README.md`, `INDEX.md`, and 70 chapter/appendix `.md` files, per
  `vulkan/README.md`) carries an *added* YAML frontmatter block, a synthesized BibTeX citation
  header, and is split per-chapter from the single official spec document — the same
  "unmodified copy only" problem as `intel_sdm/`, and on top of that, unpinned/unfetched.
- **Verdict: NOT REDISTRIBUTABLE** as currently stored.
- **Citation impact: 0.** No `REF:` citation anywhere in the Lean tree points into `references/vulkan/`
  (confirmed by repo-wide grep). Vulkan is present in the corpus but not yet load-bearing for any
  proof or model — removing or replacing it breaks no existing citations.

### 2.3 `spirv/` — 6 files, mixed license

- **`ch_01`–`ch_04` prose chapters + the prose portion of `INDEX.md`:** per the corpus's own
  `INDEX.md`, these were "directly downloaded and converted" from
  `https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html`. Same license as Vulkan above —
  the **Khronos Specification Copyright License**, unmodified-copy-only. The conversion tool that
  produced them is gone (a lost/uncommitted-tool gap per `MANIFEST.provenance.json`), and the
  chapters are reformatted Markdown with added citation headers — a derivative, which the license
  does not authorize. **Verdict: NOT REDISTRIBUTABLE.**
- **`spirv.core.grammar.json`:** fetched from `KhronosGroup/SPIRV-Headers`
  (`raw.githubusercontent.com/.../unified1/spirv.core.grammar.json`, commit
  `4965431` recorded as the latest-touching-commit surrogate). The SPIRV-Headers repository's
  `LICENSE` file is a Khronos-authored but *permissive* grant covering most files in that repo:
  *"Permission is hereby granted, free of charge, to any person obtaining a copy of this software
  and/or associated documentation files... to deal in the [material] without restriction,
  including... to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies..."* with a non-binding advisory that modifications "may mean it no longer accurately
  reflects Khronos standards." This is functionally MIT-equivalent and unrelated to the
  restrictive spec-text license above — it governs the machine-readable grammar/header artifacts,
  not the prose specification. **Verdict: REDISTRIBUTABLE-WITH-ATTRIBUTION.**
- **Citation impact: 0.** The only two repo-wide hits for `references/spirv` are (a) the literal
  citation-format string in `references/spirv/INDEX.md` and `scripts/regenerate_references.py`
  ("Use standard `/- REF: references/spirv/filename.md#anchor -/` format...") and (b) prose
  planning mentions describing the gap itself. **Zero Lean declarations
  currently cite into `references/spirv/`** — the planned SPIR-V emitter/validator work
  has not started. Removing the 5 restrictively-licensed prose files breaks nothing today, but
  would require G5 to source its ground truth differently (see §4 remedy).

### 2.4 `wasm/` — 24 files, three-way split

- **19 genuinely fetched W3C chapter files** (`syntax/`, `binary/`, `text/`, `exec/`, `valid/`,
  ~1 MB) pulled from `webassembly.github.io/spec` (the W3C WebAssembly Working Group's published
  Core Specification, e.g. `.../core/exec/runtime.html`, confirmed via the `source_url`
  frontmatter in the vendored files themselves). These are governed by the **W3C Document
  License**. Its permission grant allows copying and redistributing the document provided the W3C
  copyright/attribution notice is retained; its restriction clause — *"Publication of derivative
  works of this document for use as a technical specification is expressly prohibited"* — is aimed
  at stopping someone from republishing a modified version *as a competing spec*, not at citing or
  archiving excerpts for internal traceability. Format-converting the fetched HTML into Markdown
  for citation purposes is standard, widely-practiced vendoring for this exact license family (as
  the task brief notes, this is likely fine), but because the "derivative...for use as a technical
  specification" line is not airtight for a machine-converted full-chapter copy, I mark this
  **REDISTRIBUTABLE-WITH-ATTRIBUTION** rather than a clean REDISTRIBUTABLE, and flag the
  distinction for the owner's judgment.
- **4 hand-authored summary files** (`binary.md`, `execution.md`, `structure.md`, `text.md`) —
  confirmed by reading them: each opens with *"Not fetched by this script. This is a hand-authored
  summary... NOT the W3C Recommendation text itself... no source URL is recorded anywhere."*
  **These are not third-party material at all** — they are prose this project wrote. There is
  **no license/copyright blocker** here; open-sourcing them under the project's own Apache-2.0
  license is entirely the repository owner's call. (They remain a *separate*, already-tracked
  Law-4/TCB-T8 concern — the project's own honesty-in-provenance rule, not a redistribution-rights
  problem — and that concern is out of scope for this license audit.)
- **Citation impact — the important number for wasm:** of 94 total `REF:` citations into
  `references/wasm/`, **91 (97%) point at the four hand-authored files**, and only **3 point at
  the genuinely-fetched W3C corpus** (`Wasm/Text.lean:1`, `Wasm/Binary.lean:2`). Concretely:
  `Gasm/Targets/Wasm/Semantics.lean` (17 citations — the entire operational-semantics model) cites
  `execution.md` exclusively. Since the hand-authored files are *not* a licensing risk, this
  citation concentration is **not** a redistribution blocker — but it does mean that if the owner
  *also* wants to fix the underlying Law-4 issue (replacing self-authored prose with genuine
  vendored spec text) as part of open-sourcing, that is a much larger re-grounding effort than the
  license question alone, since 91 citations would need to be re-pointed at real spec sections.

### 2.5 `wasi/` — 3 files

- `preview1.md` (`docs.md` from `WebAssembly/WASI`, snapshot-01 branch, commit `a206794`): the
  WASI repository's `LICENSE.md` states the specification is *"Copyright © 2019–2023 the
  Contributors to the WASI Specification, published by the WebAssembly Community Group under the
  W3C Community Contributor License Agreement (CLA)."* The complementary **W3C Community Final
  Specification Agreement (FSA)** — the mechanism the CLA exists to feed into — explicitly grants
  that "the community is free to share, copy and distribute the Specification, and modify the
  Specification by making new versions." **Verdict: REDISTRIBUTABLE-WITH-ATTRIBUTION.**
- `api.md` (`api.h` from `WebAssembly/wasi-libc`, commit `6036a9f`): the wasi-libc repository
  states it is *"multi-licensed under the Apache License v2.0 with LLVM Exceptions, the Apache
  License v2.0, and the MIT License."* Fully compatible with (and one option identical to) this
  project's own Apache-2.0 license. **Verdict: REDISTRIBUTABLE-WITH-ATTRIBUTION.**
- **Citation impact: 0.** No `REF:` citation anywhere in the tree currently points into
  `references/wasi/`.

### 2.6 `zlib/` — 3 RFCs (RFC 1950, 1951, 1952)

- All three are 1996-era Informational RFCs authored by P. Deutsch et al. Each carries its
  *original* per-document notice (reproduced verbatim in the vendored files, e.g. `RFC1951.md`):
  *"Permission is granted to copy and distribute this document for any purpose and without
  charge, including translations into other languages and incorporation into compilations,
  provided that the copyright notice and this notice are preserved, and that any substantive
  changes or deletions from the original are clearly marked."* This is a genuinely permissive,
  modification-tolerant license (unlike the newer IETF Trust boilerplate, which governs later
  RFCs) — it explicitly allows changes as long as they're marked and the notice survives.
  **Verdict: REDISTRIBUTABLE-WITH-ATTRIBUTION.** (The conversion to `.md` with an added
  `source_url` frontmatter line is a reasonable candidate for "clearly marked" but the notice
  itself should be kept intact and visible, which it currently is.)
- **Citation impact:** 0 direct `REF:` citations into `references/zlib/` were found (the Lean
  Zlib implementation, e.g. `Stdlib/Zlib/Deflate.lean`, cites `docs/STDLIB_ZLIB.md` sections
  instead, which is an internal design doc, not `references/` itself).

### 2.7 `png/` — 6 files, mixed

- `RFC2083.md` (PNG spec v1.0, RFC 2083, 1997): same permissive 1996-style IETF notice as zlib
  above. **Verdict: REDISTRIBUTABLE-WITH-ATTRIBUTION.**
- `lodepng.h` / `lodepng.cpp` (Lode Vandevenne, commit `2256188`): **zlib License** — permissive,
  allows commercial use, modification and redistribution, subject to (1) not misrepresenting
  authorship, (2) marking altered versions as altered, (3) not removing the notice.
  **Verdict: REDISTRIBUTABLE-WITH-ATTRIBUTION.**
- `stb_image.h` / `stb_image_write.h` (Sean Barrett et al.): dual-licensed, redistributor's
  choice of **MIT** or **Public Domain / Unlicense**. **Verdict: REDISTRIBUTABLE-WITH-ATTRIBUTION**
  (attribution only required if the MIT branch is elected; the public-domain branch needs none —
  recommend keeping the MIT notice regardless, for clarity).
- **Citation impact:** 0 direct `REF:` citations into `references/png/` were found.

### 2.8 `windows/` — 6 files, mixed

- `pe_format.md`: fetched via GitHub raw from `MicrosoftDocs/win32` (`docs` branch,
  `desktop-src/Debug/pe-format.md`). That repository's `LICENSE` file is **CC-BY-4.0**
  (confirmed by direct fetch: *"Creative Commons Attribution 4.0 International License... You
  must retain identification of the creator(s) and indicate if You modified the material"*); its
  separate `LICENSE-CODE` (MIT) covers embedded code samples only. **Verdict:
  REDISTRIBUTABLE-WITH-ATTRIBUTION.**
- `getstdhandle.md`, `writefile.md`, `exitprocess.md`: per `regenerate_references.py`'s
  `MANIFEST`, these three were fetched with `"type": "ms_learn_html"` — scraped directly from the
  rendered `learn.microsoft.com` pages, **not** from the MicrosoftDocs GitHub source. This matters
  because the generic Microsoft Learn Terms of Use (`learn.microsoft.com/en-us/legal/termsofuse`)
  is far more restrictive on its face (*"you may not modify, copy, distribute... reproduce,
  publish... create derivative works from... any information... obtained from the Services
  [except for personal, non-commercial use] without prior written consent from Microsoft"*).
  However, that same Terms of Use document explicitly subordinates itself where a more specific
  license applies: *"Certain documentation may be subject to explicit license terms separate from
  the terms contained here. To the extent the terms conflict, the explicit license terms
  control."* Win32 API reference pages (console/getstdhandle, win32/api/fileapi/nf-fileapi-
  writefile, win32/api/processthreadsapi/nf-processthreadsapi-exitprocess) are exactly the content
  Microsoft publishes from the CC-BY-4.0-licensed `MicrosoftDocs/win32` repository and mirrors
  onto Learn — the "edit this page on GitHub" link on each of those pages points back into that
  same repo. On that basis I mark these **REDISTRIBUTABLE-WITH-ATTRIBUTION under CC-BY-4.0**
  rather than UNCLEAR, but flag the two-license-surface ambiguity explicitly: **a cheap, durable
  fix is to re-fetch these three files from the GitHub raw source (as `pe_format.md` already is)
  instead of the HTML-scraped Learn mirror**, which would remove any need to rely on the
  subordination clause at all. This is a low-cost, high-confidence remedy the owner should take
  regardless of the license conclusion above.
- `readfile.md`, `winsock2.md`: confirmed by reading them — both open with *"Not fetched by this
  script. This is a hand-authored summary... it is NOT an official Microsoft reference... no
  source URL is recorded anywhere."* **Not third-party material; no license/redistribution issue.**
  (Same Law-4 caveat as the wasm summaries — tracked separately, out of scope here.)
- **Citation impact:** 37 total `REF:` citations into `references/windows/`. **23 (62%)** go to
  the genuinely-vendored, CC-BY-4.0 files (`Win32API.lean`: 6, `PEFormat.lean`: 8,
  `Emitter.lean`: 9); **14 (38%)** go to the two hand-authored files (`Win32API.lean`: 11,
  `Spikes/Spike4HttpServer/Windows/Program.lean`: 3) — not a licensing risk, but relevant if the
  owner separately chooses to re-ground those citations in real Microsoft text.

---

## 3. Required attribution / NOTICE text (ready to paste)

For every corpus verdicted REDISTRIBUTABLE-WITH-ATTRIBUTION, paste the corresponding block(s)
below into the repository's top-level `NOTICE` file once created (Apache-2.0 projects are
expected to ship one; none exists yet in this repo).

```
This project vendors reference material from the following third parties under
references/. Each is redistributed under its own license, reproduced below.

--------------------------------------------------------------------------------
Khronos SPIR-V grammar (references/spirv/spirv.core.grammar.json)
Copyright (c) The Khronos Group Inc.
Source: https://github.com/KhronosGroup/SPIRV-Headers
Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and/or associated documentation files (the "Materials"), to deal
in the Materials without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Materials, subject to the Khronos Group's license terms in that
repository's LICENSE file. Modifications to this file may mean it no longer
accurately reflects Khronos standards.

--------------------------------------------------------------------------------
WebAssembly Core Specification (references/wasm/{syntax,binary,text,exec,valid}/)
Copyright © World Wide Web Consortium (W3C). https://www.w3.org/
Source: https://webassembly.github.io/spec
Licensed under the W3C Document License:
https://www.w3.org/copyright/document-license-2023/
This document includes material copied from or derived from the WebAssembly
Core Specification, Copyright © World Wide Web Consortium.

--------------------------------------------------------------------------------
WASI Specification (references/wasi/preview1.md)
Copyright © 2019-2023 the Contributors to the WASI Specification.
Published by the WebAssembly Community Group under the W3C Community
Contributor License Agreement (CLA) / Final Specification Agreement.
Source: https://github.com/WebAssembly/WASI

--------------------------------------------------------------------------------
wasi-libc api.h (references/wasi/api.md)
Copyright (c) The wasi-libc authors.
Source: https://github.com/WebAssembly/wasi-libc
Multi-licensed under Apache License 2.0 with LLVM Exceptions, Apache License
2.0, or MIT License, at your option.

--------------------------------------------------------------------------------
RFC 1950, RFC 1951, RFC 1952 (references/zlib/)
RFC 1950/1951 Copyright (c) 1996 L. Peter Deutsch (and Jean-Loup Gailly for
RFC 1950). RFC 1952 (gzip) similarly attributed to its IETF authors.
"Permission is granted to copy and distribute this document for any purpose
and without charge, including translations into other languages and
incorporation into compilations, provided that the copyright notice and this
notice are preserved, and that any substantive changes or deletions from the
original are clearly marked."
Source: https://www.rfc-editor.org/rfc/rfc195{0,1,2}.txt

--------------------------------------------------------------------------------
RFC 2083 — PNG Specification (references/png/RFC2083.md)
Copyright (c) 1997 T. Boutell, et al.
Same permission notice as above.
Source: https://www.rfc-editor.org/rfc/rfc2083.txt

--------------------------------------------------------------------------------
LodePNG (references/png/lodepng.h, lodepng.cpp)
Copyright (c) 2005-2026 Lode Vandevenne
Licensed under the zlib License:
  This software is provided 'as-is', without any express or implied warranty.
  In no event will the authors be held liable for any damages arising from
  the use of this software. Permission is granted to anyone to use this
  software for any purpose, including commercial applications, and to alter
  it and redistribute it freely, subject to the following restrictions:
  1. The origin of this software must not be misrepresented; you must not
     claim that you wrote the original software.
  2. Altered source versions must be plainly marked as such.
  3. This notice may not be removed or altered from any source distribution.
Source: https://github.com/lvandeve/lodepng

--------------------------------------------------------------------------------
stb_image / stb_image_write (references/png/stb_image.h, stb_image_write.h)
Copyright (c) 2017 Sean Barrett
Dual-licensed, at the user's option:
  (A) MIT License, or
  (B) Public Domain (Unlicense, www.unlicense.org)
Source: https://github.com/nothings/stb

--------------------------------------------------------------------------------
Microsoft Win32 documentation (references/windows/pe_format.md, getstdhandle.md,
writefile.md, exitprocess.md)
Copyright (c) Microsoft Corporation.
Licensed under the Creative Commons Attribution 4.0 International License
(CC BY 4.0): https://creativecommons.org/licenses/by/4.0/
Source: https://github.com/MicrosoftDocs/win32
--------------------------------------------------------------------------------
```

No attribution text is provided for `intel_sdm/`, `vulkan/`, or the 5 restrictively-licensed
`spirv/` prose files — they are not redistributable in their current form (§4).

---

## 4. BLOCKERS FOR OPEN-SOURCING

These items must not ship in a public Apache-2.0 repository without either a change to what is
stored, or explicit permission/legal clearance from the owner. Ordered by severity × footprint.

### BLOCKER 1 — `references/intel_sdm/` (928 files, NOT REDISTRIBUTABLE)

- **Why:** Intel's license permits only an *unmodified* copy; this corpus is a reformatted,
  table-flattening, per-chapter Markdown conversion with no recorded source edition/date pin.
  928 files is 89% of the entire `references/` corpus.
- **Impact if simply deleted:** 263 `REF:` citations across 33 files break — the entire
  `Gasm/Targets/X86_64/**` tree (encoder, decoder, instruction registry, both fuzzers, the
  performance model) loses its cited ground truth. This is the single most disruptive corpus to
  touch in the whole project.
- **Recommended remedy (in order of preference):**
  1. **Remove the vendored copy; replace with a fetch-on-demand script** that downloads the
     official Intel PDF (or the specific, dated public URL, e.g. `cdrdv2-public.intel.com/...`)
     into a local, gitignored cache at build/dev time, and change every `REF:` citation from a
     path into `references/intel_sdm/...md` to a `(volume, page range, section title)` locator
     plus the public PDF URL — i.e., cite by locator, don't vendor the text. This is exactly what
     Intel's license already allows (an unmodified copy, held locally, not redistributed by this
     project) and preserves the citation discipline Law 4 wants.
  2. Alternatively, obtain **explicit written permission from Intel** to redistribute the
     converted/chunked form — unlikely to be granted in practice for a hobby/research project,
     but the only way to keep the current file layout as-is.
  3. Not recommended: keeping only page/section *citations* without any local text at all removes
     the "ground truth in the repo" property Law 4 exists to guarantee; option 1 is preferred
     because it keeps a real, unmodified, legally-held local copy for contributors to check
     against, it just isn't redistributed *from this repo*.

### BLOCKER 2 — `references/vulkan/` (72 files, NOT REDISTRIBUTABLE)

- **Why:** Khronos Specification Copyright License, unmodified-copy-only; corpus is reformatted
  per-chapter Markdown with synthesized frontmatter, never fetched/pinned to begin with.
- **Impact if deleted:** **Zero** `REF:` citations exist into this corpus today — no Lean
  declaration currently depends on it.
- **Recommended remedy:** Remove the vendored chapters. Replace with a link-only citation scheme
  (cite `https://registry.khronos.org/vulkan/specs/1.3-extensions/html/vkspec.html#<anchor>` plus
  section number/title, no local copy) for any future Vulkan/SPIR-V-adjacent work. Given zero
  current citations, this is a low-cost, zero-regression fix — do this one first as a template
  for how the Intel remedy should look.

### BLOCKER 3 — `references/spirv/ch_01`–`ch_04` + prose in `INDEX.md` (5 files, NOT REDISTRIBUTABLE)

- **Why:** Same Khronos Specification Copyright License as Vulkan; conversion tool is lost, so
  the corpus isn't even reproducible today.
- **Impact if deleted:** **Zero** current `REF:` citations. The planned SPIR-V emitter/validator
  work had not yet started, so no code needed
  re-grounding.
- **Recommended remedy:** Remove the 5 prose files; keep `spirv.core.grammar.json` (which is
  separately, permissively licensed — not a blocker) as the machine-readable ground truth, and
  have G5 cite `registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html#<anchor>` by link+section
  rather than vendoring prose. This is the cheapest blocker to clear in the whole list.

### BLOCKER 4 (soft / recommendation, not a hard block) — `references/windows/{getstdhandle,writefile,exitprocess}.md`

- **Why flagged at all:** these are provably CC-BY-4.0 (§2.8), so this is not a redistribution
  blocker — but they were fetched via HTML-scrape from `learn.microsoft.com` rather than from the
  authoritative CC-BY-4.0 GitHub source, which is unnecessary legal-ambiguity surface for zero
  benefit.
- **Recommended remedy:** Before publishing, re-run the fetch against the `MicrosoftDocs/win32`
  GitHub raw source (the same path `pe_format.md` already uses) so all four Windows-doc files
  share one unambiguous CC-BY-4.0 provenance trail. Cheap, mechanical, no citation impact (the 23
  citations into these files are keyed by content/anchor, not fetch method).

### Not a blocker, but flag for the owner — self-authored files masquerading as vendored

`references/wasm/{binary,execution,structure,text}.md` (91 of 94 wasm citations) and
`references/windows/{readfile,winsock2}.md` (14 of 37 windows citations) carry **no license risk**
— this project owns the copyright on its own prose. They are already disclosed on-disk and in
`MANIFEST.provenance.json`, and were tracked as a separate integrity concern (now
`docs/REFERENCE_INDEX.md` §10 and Law 4)
about whether the project's models are actually derived from vendored ground truth. That is a
correctness/rigor issue for the project's own standards, not a licensing obstacle to
open-sourcing — but the owner should not read a clean license verdict here as "this content is
fine" in the Law-4 sense; the two questions are independent and this document only answers the
license one.

---

## 5. Summary of citation impact (quantified)

| Corpus at risk | Direct `REF:` citations | Files citing | Note |
|---|---|---|---|
| `intel_sdm/` | **263** | 33 | Entire `Gasm/Targets/X86_64/**` — encoder, decoder, registry, both fuzzers, perf model |
| `vulkan/` | **0** | 0 | No current dependents |
| `spirv/` prose (ch_01–04) | **0** | 0 | No current dependents; G5 task not started |
| `spirv.core.grammar.json` | 0 direct (not a blocker) | — | Reserved for future G5 work |
| `wasm/` genuine W3C files | 3 | 2 | Not a blocker (CC-BY/W3C, redistributable) |
| `wasm/` hand-authored files | 91 | 10 | Not a license risk (own copyright); separate Law-4 concern |
| `wasi/` | 0 | 0 | Not a blocker |
| `zlib/` | 0 direct | — | `Stdlib/Zlib/Deflate.lean` cites `docs/STDLIB_ZLIB.md`, not `references/` directly |
| `png/` | 0 direct | — | Not currently cited directly |
| `windows/` genuine (CC-BY-4.0) | 23 | 3 | Not a blocker |
| `windows/` hand-authored | 14 | 2 | Not a license risk; separate Law-4 concern |

---

## 6. Methodology

- Corpus shapes, file counts, and fetch provenance: `references/MANIFEST.provenance.json`,
  `references/MANIFEST.sha256`, `scripts/regenerate_references.py`'s `MANIFEST` dict.
- Citation counts: repo-wide `grep` for `REF: references/<corpus>` (and, for `wasm`/`windows`,
  split further between the hand-authored and genuinely-vendored file names within each corpus)
  against the full working tree on branch `claude/codebase-review-sonnet-4fe3c4` at the time of
  this audit (2026-08-27).
- License texts: fetched or searched from the primary upstream source in each case (Intel's own
  SDM PDFs, `registry.khronos.org/speccopyright.html` and `docs.vulkan.org` for Khronos,
  `w3.org/copyright/document-license-2023` for W3C, `trustee.ietf.org` and the RFCs' own printed
  notices for IETF, `learn.microsoft.com/.../termsofuse` and `github.com/MicrosoftDocs/win32` for
  Microsoft, and the respective GitHub repos' `LICENSE` files for LodePNG, stb, wasi-libc, and
  SPIRV-Headers) — see inline citations throughout §2.
- This document does not modify any file under `references/`; it is a standalone audit artifact.
