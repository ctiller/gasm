# Win32 windowing normative-source intake

> **Status:** research and ingestion plan only.  This is not the future normative
> `docs/TARGETS/WIN32_WINDOWING.md`, is not `REF:`-citable implementation authority, and does not
> claim that the current graphics prototype conforms to Win32.

## 1. Dependency and authority boundary

Win32 windowing is a platform/library capability model.  It is separate from the host ISA, SPIR-V
shader semantics, and Vulkan API semantics.  A selected product profile may compose all four, but
none defines another.  The first normative model must preserve exact API identities and observable
ordering while leaving final proof and emission authority with `VerifiedProgram` and
`VerifiedExportSet`.

The local `Spikes/GraphicsFoundation/Window.lean` and `Presentation.lean` files are useful
adversarial prototypes, not normative sources.  Do not edit their convenient model into the Win32
contract.  Build the contract from pinned official sources, then prove an explicit refinement from
any retained prototype.

## 2. Reproducible source intake

Do not vendor Microsoft prose.  Register one slug per citable page in `references.json`; cache the
exact fetched bytes under gitignored `.cache/references`.  Prefer commit-pinned raw Markdown from
the official Microsoft documentation repositories.  Each entry should use corpus `windows`, media
type `markdown`, heading anchors, license `cc-by-4.0`, distribution
`attribution-required`, an exact SHA-256, fetch date, reviewer, and review note.

Research on 2026-08-30 resolved these source commits:

- `MicrosoftDocs/sdk-api` docs commit `4502fff176b3b56beddb6a63c9f980377b11ba9b`;
- `MicrosoftDocs/win32` docs commit `ae532eec351953d128dd9e65f78d9edacb56f4b5`.

They are research-time pins, not silently approved registry updates.  The intake reviewer must
resolve and review the exact commit to be registered.  Initial registration is manual: fetch the
exact raw bytes, inspect them, hash them, add the schema entry, then run
`scripts/check_references.py --self-test`, refresh each new slug, and run the offline audit.  Never
use a registration shortcut that invents review metadata.

Minimum SDK API pages under `sdk-api-src/content/winuser/`:

- `nf-winuser-registerclassexw.md`, `ns-winuser-wndclassexw.md`;
- `nf-winuser-createwindowexw.md`, `nf-winuser-destroywindow.md`;
- `nf-winuser-getmessagew.md`, `ns-winuser-msg.md`;
- `nf-winuser-translatemessage.md`, `nf-winuser-dispatchmessagew.md`;
- `nf-winuser-defwindowprocw.md`, `nf-winuser-postquitmessage.md`;
- `nc-winuser-wndproc.md`, `nf-winuser-sendmessagew.md`.

Minimum conceptual pages under `desktop-src/`:

- `winmsg/about-window-classes.md`, `winmsg/about-messages-and-message-queues.md`;
- `winmsg/wm-close.md`, `winmsg/wm-destroy.md`, `winmsg/wm-quit.md`, `winmsg/wm-size.md`;
- `inputdev/wm-keydown.md`, `inputdev/wm-keyup.md`, `inputdev/wm-char.md`;
- `inputdev/wm-mousemove.md`, `inputdev/wm-lbuttondown.md`,
  `inputdev/wm-lbuttonup.md`.

The existing `windows-pe-format` source owns PE import-directory facts.  The Win32 target should
state exact `User32.dll` import symbols; API-set and runtime forwarding behavior stays outside the
first claim.

## 3. First-model boundary

The first model should select only non-system key down/up/character messages, mouse move/left
button down/up, and resize.  System keys, wheel and X buttons, raw input, pointer/touch, capture,
IME, accelerators, dialogs, paint, timers, and DPI behavior are unselected and impose no proof
burden.

The normative design must account for these semantics rather than smoothing them into a simple
event queue:

- callbacks may be reentrant during window creation, destruction, message retrieval, default
  processing, and synchronous message sending;
- window ownership is a relation to the creating thread, not a function reconstructed from handle
  bits;
- message retrieval has positive-message, quit, and error outcomes;
- closing may be declined; destruction does not itself post quit; a quit message belongs to the
  thread queue and is not dispatched to the window procedure.

Author `docs/TARGETS/WIN32_WINDOWING.md` with exact source anchors before Lean implementation.
Then run reference, license, publishability, orphan, and diff/forbidden-mechanism gates.  Any finite
bound must be classified as mathematical, capability/resource, runtime-enforced, environmental, or
proof-search only; exhaustion and cleanup remain explicit.
