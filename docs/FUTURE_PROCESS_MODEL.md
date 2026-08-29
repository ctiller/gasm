# Deferred Hosted-Process Extension

**Status:** design constraints for future work, not a current implementation stage, public API, or
acceptance dependency. The M0–M9 concurrency path supports one host process with multiple CPU
threads, plus bare-metal CPU/PE execution and independently selected heterogeneous device domains.
It does not implement `fork`, `_Fork`, `vfork`, `exec`, `posix_spawn`, `CreateProcess`, process
observation/reaping, cross-process handle transfer, or process-shared robust synchronization.

This document preserves the process-model lessons learned during memory-model review without making
every current implementer prove an unused operating-system subsystem. Work here begins only when a
consumer selects a concrete process capability and its reference-intake decision is accepted. The
historical all-in-one M6-P/M6-PS stage names are retired before implementation; only M0–M9 are current
stage identifiers.

## 1. Boundary With the Current Model

“One host process” does **not** mean “one global address space.” A current or future single-process
program may coordinate:

- one host CPU virtual-address domain;
- one or more device virtual-address and resource-binding domains;
- SPIR-V storage-class and Vulkan device/queue/resource scopes;
- sparse, aliased, external, device-group, IOMMU and registered-memory bindings; and
- transport or persistence objects that are not byte-addressed memory at all.

Those domains use the target-indexed agent, reference, location, binding-generation, relation and
consequence interfaces in `docs/MEMORY_MODEL.md` §§4 and 11. GPU/device agents are not disguised as
host threads and are not scheduled by M3. Conversely, adding a GPU domain does not create a host
process, PID namespace, process handle table, zombie/reap record, or `fork` semantics.

The current interfaces remain open to a later process composition by preserving opaque domain/owner
qualification, generative identities, dynamic bindings, explicit environment agents, relational
boundary outcomes and resource-specific failure dispositions. They must not expose a guessed public
`ProcessState` constructor or theorem that quantifies over all agents as though they shared the host
CPU address domain. Openness is the present obligation; process implementation is not.

Current whole-program termination remains strict. Terminating the implicit root host process or a
bare-metal machine must account for every live thread context, terminal bundle, guard, loan, join
right and other linear obligation under `docs/MEMORY_MODEL.md` §6.4. It is not evidence that the
multi-process rules below have been implemented.

## 2. Capability-Indexed Future Profiles

A future process model is a family of independently selected certificates, not one platform-sized
proof. Suggested feature keys are descriptive capability labels, not roadmap stages:

| Capability | Minimum semantic surface |
|---|---|
| `P-IDENTITY[platform]` | Generative process, image, address-domain and failure-domain identities plus external-name binding/reuse rules; no creation, terminal-status or wait semantics by itself |
| `P-CREATE[operation]` | Only the selected creation operation and result branches, such as `posix_spawn`, `fork`, `_Fork`, `vfork`, `clone3`, or `CreateProcess` |
| `P-IMAGE[operation]` | Only a selected image-replacement operation and its commit/failure points |
| `P-TERMINAL[mode]` | Only selected normal/forced termination and status-availability consequences plus resource dispositions |
| `P-OBSERVE[mechanism]` | Only selected repeatable observation, status consumption/reaping, persistent lifecycle-object wait and external-name-reuse behavior |
| `P-RELATION[feature]` | Only selected parent/reaper/subreaper, namespace, job, group or cascade behavior |
| `P-MEMORY[mode]` | Only selected private-copy, shared-mapping, sparse/external mapping or environment-interference behavior |
| `P-CHANNEL[mechanism]` | Only selected pipe/socket/message/shared-memory/descriptor/handle/object derivation mechanisms |
| `P-SHARED-SYNC[profile]` | Only selected process-shared wait-key, robust owner-death, recovery/poison and native realization rules |

For example, an opaque `posix_spawn` child connected by one pipe should require `P-IDENTITY`, that
spawn constructor, its selected terminal behavior and that pipe channel—not `fork`, `vfork`,
`clone3`, pidfds, shared mappings or
`SCM_RIGHTS`. A Windows program using `CreateProcess` with one inherited pipe should not inherit job,
`DuplicateHandle`, socket-transfer or shared-memory proofs. A selected capability brings its complete
authority, lifecycle, failure, platform and validation closure; unselected constructors bring none.

The common future topology may eventually need information equivalent to:

```text
SystemState
  generative process instances and external-name bindings
  process image and host address-domain generations
  selected local handle/descriptor tables and shared kernel/backing objects
  selected status/reap records, parent/reaper/job relations and failure domains
  host threads, execution agents, platform state and heterogeneous device domains

ProcessState processInstance
  current image and host address-domain generation
  selected namespace/table identities
  owned logical threads
  selected lifecycle relations and failure domain
```

This is required information content, not a frozen Lean record. Address domains and tables are
referenced objects because selected clone operations may share them, while ordinary process creation
usually creates distinct instances.

## 3. Creation, Images, and Mapping Authority

Every creation operation is result-indexed. Failure creates no child identity, address domain, image,
external-ID binding, status/observation resource, handle/descriptor entry, close obligation, parent
suspension or borrowed world unless the exact platform contract explicitly says an earlier side
effect occurred. Success creates only the resources and relationships selected for that operation.
Raw PID, TID, fd, handle or result bits never manufacture their erased identities or authority.

The portable `fork` abstraction, if selected, creates fresh logical private regions whose initial
contents equal the corresponding parent contents and whose later writes are isolated. It also applies
the selected shared/omitted/reset mapping dispositions and rebases typed views and pointer-slot
bindings through a generative lifecycle witness. It does **not** require user programs to model page
tables, physical pages or copy-on-write allocation.

A Linux kernel/VM-verification profile may optionally refine that abstraction with physical COW. In
that refinement, shared snapshot backing carries only the authority decomposition derived from the
pre-fork grants; it never receives a blanket exclusive grant merely because a fault occurred. Before
**any store-class effect** to frozen backing—ordinary store, atomic store/RMW, successful exclusive
store, or platform-origin store such as child-TID publication—the kernel transition must allocate or
select permitted backing, copy as required, generation-rebind the affected mapping and install exactly
the restored logical grant before the effect resolves. A negative control that requires this only for
ordinary writes is itself invalid. The refinement then proves the portable initial-equality and later-
isolation contract.

Shared mappings preserve backing identity and create only the read-shared, registered-atomic,
partitioned or environment-interference grants justified by the selected split. Mapping inheritance
never duplicates an `Exclusive` grant to common mutable backing. Omitted/reset mappings create no
stale view or pointer-slot provenance. Copied mutex bytes create neither a guard nor ownership.

An opaque child or replacement image is an environment agent, not code that silently disappears from
the model. For every inherited/shared writable resource its selected profile must do one of:

1. install an environment/havoc grant over the exact footprint and permitted effects, downgrading or
   transferring conflicting parent authority;
2. expose all mutation through explicitly modeled channels with their own authority and visibility;
   or
3. forbid writable sharing.

The same rule applies to shared open-file descriptions/offsets, inherited events, pipes, sockets,
filesystem/device state and other kernel objects. A parent cannot retain verified exclusive authority
while opaque code can mutate the same object.

If later selected, multithreaded `fork` retains only the calling thread and enters the platform's
restricted child phase; at-fork callbacks, `_Fork`, `vfork`, exec, spawn and Windows creation remain
distinct constructors. A `vfork`-like profile uses a scoped non-owning address-domain borrow and
parent suspension plus `MustExecOrExit`; it does not create a private world. Image replacement keeps
or changes identities only as its platform contract says and invalidates retired-image views at its
commit point. Physical COW remains optional even when these logical lifecycle rules are selected.

## 4. Observation, Handles, and Failure

`JoinRight` remains a high-level one-shot task/thread result contract. Process terminality, status
availability, notification, repeatable observation, POSIX status consumption/reaping, external-name
reuse and lifecycle-object reclamation are separate consequences. A process-backed task adapter must
own the required process resources and an explicit result/IPC channel, then prove that composition;
process exit never returns arbitrary private address-space authority in a terminal bundle.

Each selected descriptor/handle/object mechanism distinguishes:

- local entry identity and binding generation;
- intermediate open-file description/provider object and underlying object identity;
- rights, inheritability and independent close obligations;
- copy/alias, move/donation, attenuation, inheritance, name import and object-specific export/import;
- publication, receiver acceptance, source retention/closure and failure atomicity.

Thus an `SCM_RIGHTS`-like operation can create a fresh alias while retaining the sender entry, while a
`DuplicateHandle`-like operation may transform rights and may close the source on a result-dependent
path. Numeric equality across namespaces proves nothing.

Every future process belongs to an explicit failure domain, and each selected resource/effect has a
non-vacuous disposition: survive, close, invalidate, owner-dead, orphan/reparent, continue, cancel,
leak, or a precisely bounded indeterminate state. A selected profile's disposition table is total
over its reachable resource classes and has no wildcard. “Indeterminate” is not a default escape
hatch, may not consume an in-model linear resource, and is admitted only for a named external
resource/effect class with pinned platform uncertainty or an explicit TCB rule. Forced termination
invalidates only what that domain and those resource rules say; it is not normal obligation discharge
or global-world invalidation.

Robust owner-death recovery is a quarantined repair state. `acquiredNeedsRecovery` may grant the exact
write capability required to inspect and repair inconsistent protected data, but it grants no healthy
invariant-backed guard or authority usable by ordinary clients. A successful checked repair restores
the invariant and atomically promotes the exceptional guard to `acquiredHealthy`; release without the
required repair follows the selected poison/not-recoverable transition. Windows abandoned ownership
and POSIX robust consistency remain separate profiles.

## 5. Boundary and Validation Rules

Every future native lifecycle/bootstrap boundary consumes the canonical boundary-profile closure and
class-level prevention rules in `docs/MEMORY_MODEL.md` §§3 and 12; this document does not redefine
them. Its process-specific delta is that the registry names the exact selected process capabilities
and result branches. An opaque child uses a pinned platform/TCB origin plus the environment-
interference rules in §3 and needs no application-code theorem. A verified child additionally needs
the exact child artifact and application-entry witness. Neither case may authorize a transition by
ordering unconstrained ghost events.

Reference intake is capability-indexed. Before selecting a capability, pin only its applicable source
families:

- POSIX/Linux creation and image operations: exact POSIX edition plus kernel/UAPI/libc behavior for
  the chosen operation, result branches, mapping dispositions, at-fork/restricted-child rules,
  descriptor disposition, signals, PID/pidfd identity and any selected wait/reap/reparent behavior;
- Windows creation/lifecycle: exact supported version and contracts for selected `CreateProcess`
  flags/results, loader/root initialization, process/thread objects, observation/status/termination,
  loader lock and `DllMain`, inheritance/attribute lists, jobs or transfer mechanisms actually used;
- process-shared synchronization: exact shared backing/key lifetime, robust-list ABI, owner-death,
  recovery/consistent/poison, interruption and native atomic/emission behavior; and
- asynchronous lifecycle contexts: exact handler/callback entry, nesting, return/resume/propagation/
  unwind/fatal outcomes and callable restrictions for only the contexts selected by the operation.

The decision that opens this work must name its first consumer, selected capabilities, canonical
profile-closure representation, reference hashes, validation matrix and smallest reusable proof
surface. Until then these notes constrain future compatibility but impose no process theorem,
process-source intake, multiprocess runner or process API on M0–M9.
