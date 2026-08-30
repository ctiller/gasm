# Spike 4: verified streaming HTTP request lifecycle

Spike 4 is a universal, arbitrary-finite-input example for the sole
`Gasm.Core.Platform.VerifiedProgram`. It verifies the same logical request lifecycle on three
profiles:

- Windows x86-64 plus the Gasm verified-component runtime;
- Linux x86-64 plus the Gasm verified-component runtime; and
- WASI plus the Gasm verified-component runtime.

These profiles intentionally do **not** claim that the artifacts run on a stock OS without that
runtime. Windows links `GASMRT.dll`, Linux uses a reserved Gasm runtime call, and Wasm imports
`gasm:verified/http-parser`. The capability composition names those requirements and the final
artifact/provider certificates prove their exact linkage.

## 1. High-Level Architecture & Protocol State Machine

### 1.1 Supported HTTP 1.1 Specification Subset

The streaming request-line parser accepts the `Stdlib.Http11` request-line grammar and routes `/`,
`/status`, and other valid targets to 200, status JSON, and 404 responses respectively. Malformed
request lines produce 400; over-budget request lines produce 414. Header/body handling and a
persistent multi-request accept loop are future extensions, not claims of this spike.

## 2. Linear Socket Obligations & Resource Discipline

### 2.1 Socket Lifecycle Rules

Each request scope accepts, receives, sends, and closes. Completion, malformed input, and resource
exhaustion all reach the close edge; resource failure cannot silently abandon the request scope.

### Streaming and finite resources

`Spikes/Spike4HttpServer/Runtime.lean` accepts every finite `ByteArray`; it has no `HttpRoute`
proxy, literal-request allowlist, or caller-selected input domain. The request-line component:

- reads in chunks of at most 256 bytes;
- retains at most 1024 request-line bytes;
- returns `resourceExhausted` when that request scope exceeds its budget;
- maps exhaustion to an explicit `414 URI Too Long` response; and
- closes the request connection, permitting the next logical request scope to start cleanly.

Thus the proof does not assume infinite memory. Allocation/retention failure is an ordinary,
recoverable result. `resource_failure_does_not_poison_next` proves the logical recovery property.
The current emitted executables process one request and terminate; `serverEnvironmentSpec` therefore
observes the first request in an arbitrary environment. The reusable logical runtime is defined over
request lists so a later accept loop can reuse the same request-scope recovery theorem.

## Verified parser component and ABI boundary

`Spikes/Spike4HttpServer/ParserCapability.lean` publishes the streaming parser as a nominal
`.parseChunk` boundary. Its result-dependent contract consumes one open-request obligation and:

- preserves it when more input is needed;
- discharges it on completion; or
- discharges it on resource exhaustion.

The `ContextBoundaryRealization` ties the exact parser implementation and artifact identities to
physical executions, entry/exit relations, physical admissibility, and the obligation transition.
`StreamingParserDriverConnection` then proves once that `driveRequest` obtains its route from that
realization. Target adapters consume this reusable connection; ordinary callers do not replay the
parser or ABI proof.

## 3. Cross-Target Architectural Realization

### 3.1 x86-64 Windows (`GASMRT.dll`)

The final PE imports the verified parser runtime at its exact IAT slot.

### 3.2 WebAssembly (`.wasm`)

The final Wasm module imports the verified parser component and exports no extra callable function
boundary.

### 3.3 x86-64 Linux (ELF)

The final ELF uses five exact reserved Gasm runtime call sites; this is not a stock kernel syscall.

### Typed lifecycle realization

Each target program performs five typed lifecycle calls: listen, accept, receive/parse, send, and
close. `Spikes/Spike4HttpServer/Equivalence.lean` proves reusable edge lemmas and composes them into
exact lifecycle certificates rather than evaluating a closed interpreter oracle.

The Windows capability is linked to the exact PE import/IAT entry, Linux to five exact runtime-call
sites, and WASI to the exact import and module body. Adapter connection records prove that all three
physical hooks return the route produced by the verified parser component.

## 4. Semantic Trace Equivalence & VerifiedProgram Contract

### Whole-program certificates

The module constructs ownership-scoped certificates for:

1. final artifact serialization and exact callable exports;
2. provider coverage and linkage;
3. entry-context establishment;
4. target termination/admissibility; and
5. universal observable behavior.

`VerifiedProgram.compose` combines them into:

- `spike4VerifiedWindowsProgram`;
- `spike4VerifiedLinuxProgram`; and
- `spike4VerifiedWasiProgram`.

All three quantify over the canonical `Environment`. Native outcomes distinguish returned/halted
execution from fuel exhaustion; WASI preserves its explicit completion/resource outcome. Closed
regression probes remain supplemental tests and are not used to narrow the verified domain.
