/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean

namespace Spikes.GraphicsFoundation.Vulkan

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive ResourceKind where
  | device | memory | buffer | binding | descriptor | commandBuffer | fence | submission
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Generational identity scoped to a parent device. -/
structure Handle (kind : ResourceKind) where
  device : Nat
  slot : Nat
  generation : Nat
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev DeviceHandle := Handle .device

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev MemoryHandle := Handle .memory

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev BufferHandle := Handle .buffer

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev BindingKey := Handle .binding

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev DescriptorHandle := Handle .descriptor

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev CommandBufferHandle := Handle .commandBuffer

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev FenceHandle := Handle .fence

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev SubmissionHandle := Handle .submission

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure Limits where
  maxMemoryAllocations : Nat
  maxDeviceMemoryBytes : Nat
  maxBuffers : Nat
  maxDescriptors : Nat
  maxCommandBuffers : Nat
  maxSubmissions : Nat
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure DeviceCapability where
  loaderAvailable : Bool
  computeQueueAvailable : Bool
  limits : Limits
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive Error where
  | loaderUnavailable
  | noComputeQueue
  | deviceAlreadyCreated
  | deviceLost
  | cooperationCancelled
  | outOfHostMemory
  | outOfDeviceMemory
  | poolExhausted (kind : ResourceKind)
  | invalidHandle (kind : ResourceKind)
  | wrongParentDevice
  | staleGeneration (kind : ResourceKind)
  | rangeOutOfBounds
  | memoryNotHostVisible
  | memoryAlreadyMapped
  | memoryNotMapped
  | resourceInUse (kind : ResourceKind)
  | invalidCommandState
  | invalidFenceState
  | fenceNotReady
  | submissionNotFound
  | cleanupObligationsRemain
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive AuditEvent where
  | deviceCreated (device : DeviceHandle)
  | memoryAllocated (memory : MemoryHandle) (bytes : Nat)
  | memoryMapped (memory : MemoryHandle)
  | memoryUnmapped (memory : MemoryHandle)
  | bufferCreated (buffer : BufferHandle) (bytes : Nat)
  | bufferBound (buffer : BufferHandle) (memory : MemoryHandle) (offset : Nat)
  | descriptorUpdated (descriptor : DescriptorHandle) (buffer : BufferHandle)
  | commandRecorded (command : CommandBufferHandle)
  | submitted (submission : SubmissionHandle) (fence : FenceHandle)
  | cooperationStopped
  | waitAbandoned (fence : FenceHandle)
  | deviceCompleted (submission : SubmissionHandle)
  | fenceObserved (fence : FenceHandle)
  | hostReuseGranted (submission : SubmissionHandle)
  | rangeAvailableToHost (submission : SubmissionHandle) (memory : MemoryHandle) (offset bytes : Nat)
  | rangeVisibleToHost (submission : SubmissionHandle) (memory : MemoryHandle) (offset bytes : Nat)
  | lostUseRetired (submission : SubmissionHandle)
  | deviceWasLost
  | resourceDestroyed (kind : ResourceKind) (slot generation : Nat)
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure MemoryAllocation where
  handle : MemoryHandle
  bytes : Nat
  hostVisible : Bool
  mapped : Bool := false
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure MemorySlice where
  binding : BindingKey
  buffer : BufferHandle
  memory : MemoryHandle
  offset : Nat
  bytes : Nat
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure Buffer where
  handle : BufferHandle
  bytes : Nat
  binding : Option MemorySlice := none
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure Descriptor where
  handle : DescriptorHandle
  buffer : Option BufferHandle := none
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive CommandState where
  | initial | recording | executable | pending | invalidAfterDeviceLoss
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive Command where
  | dispatch (descriptor : DescriptorHandle) (x y z : Nat)
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure CommandBuffer where
  handle : CommandBufferHandle
  state : CommandState := .initial
  commands : List Command := []
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive FenceState where
  | unsignaled | pending | signaled | deviceLost
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure Fence where
  handle : FenceHandle
  state : FenceState := .unsignaled
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive SubmissionPhase where
  | inFlight
  | completedButUnobserved
  | hostReuseAllowed
  | deviceLostUseRetired
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- An in-flight submission is the device agent's lease over referenced resources. -/
structure Submission where
  handle : SubmissionHandle
  commandBuffer : CommandBufferHandle
  fence : FenceHandle
  descriptors : List DescriptorHandle
  bindings : List MemorySlice
  phase : SubmissionPhase := .inFlight
  hostObservations : Nat := 0
  availableToHost : List MemorySlice := []
  visibleToHost : List MemorySlice := []
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
inductive DevicePhase where
  | active | lost
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
structure State where
  capability : DeviceCapability
  device : Option DeviceHandle := none
  devicePhase : DevicePhase := .active
  acceptsSubmissions : Bool := true
  nextSlot : Nat := 1
  generations : List (ResourceKind × Nat × Nat) := []
  memories : List MemoryAllocation := []
  buffers : List Buffer := []
  descriptors : List Descriptor := []
  commandBuffers : List CommandBuffer := []
  fences : List Fence := []
  submissions : List Submission := []
  audit : List AuditEvent := []
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
abbrev Transition (α : Type) := State → Except Error (α × State)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def requireDeviceIdentity (s : State) : Except Error DeviceHandle :=
  match s.device with | some d => .ok d | none => .error (.invalidHandle .device)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def requireOperationalDevice (s : State) : Except Error DeviceHandle := do
  let d ← requireDeviceIdentity s
  if s.devicePhase == .lost then throw .deviceLost
  pure d

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def currentGeneration (s : State) (kind : ResourceKind) (slot : Nat) : Option Nat :=
  (s.generations.find? (fun x => x.1 == kind && x.2.1 == slot)).map (fun x => x.2.2)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def checkHandle (s : State) (expected : ResourceKind) (h : Handle expected) : Except Error Unit := do
  let d ← requireDeviceIdentity s
  if h.device != d.device then throw .wrongParentDevice
  match currentGeneration s expected h.slot with
  | none => throw (.invalidHandle expected)
  | some generation => if generation == h.generation then pure () else throw (.staleGeneration expected)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def freshHandle (s : State) (kind : ResourceKind) : Handle kind × State :=
  let deviceId := s.device.map (fun d => d.device) |>.getD s.nextSlot
  let h : Handle kind := { device := deviceId, slot := s.nextSlot, generation := 0 }
  (h, { s with nextSlot := s.nextSlot + 1, generations := (kind, h.slot, h.generation) :: s.generations })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def retireHandle (s : State) (kind : ResourceKind) (slot generation : Nat) : State :=
  { s with
    generations := s.generations.map fun x =>
      if x.1 == kind && x.2.1 == slot then (kind, slot, generation + 1) else x
    audit := s.audit ++ [.resourceDestroyed kind slot generation] }

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def createDevice : Transition DeviceHandle := fun s =>
  if !s.capability.loaderAvailable then .error .loaderUnavailable
  else if !s.capability.computeQueueAvailable then .error .noComputeQueue
  else if s.device.isSome then .error .deviceAlreadyCreated
  else
    let h : DeviceHandle := { device := s.nextSlot, slot := s.nextSlot, generation := 0 }
    .ok (h, { s with
      device := some h
      nextSlot := s.nextSlot + 1
      generations := [(.device, h.slot, h.generation)]
      audit := s.audit ++ [.deviceCreated h] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def allocateMemory (bytes : Nat) (hostVisible : Bool) : Transition MemoryHandle := fun s => do
  let _ ← requireOperationalDevice s
  if s.memories.length >= s.capability.limits.maxMemoryAllocations then throw (.poolExhausted .memory)
  if bytes > s.capability.limits.maxDeviceMemoryBytes - min s.capability.limits.maxDeviceMemoryBytes (s.memories.foldl (fun n m => n + m.bytes) 0) then
    throw .outOfDeviceMemory
  let (h, s') := freshHandle s .memory
  let memory : MemoryAllocation := { handle := h, bytes := bytes, hostVisible := hostVisible }
  pure (h, { s' with memories := memory :: s'.memories, audit := s'.audit ++ [.memoryAllocated h bytes] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def mapMemory (h : MemoryHandle) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .memory h
  let some memory := s.memories.find? (fun m => m.handle == h) | throw (.invalidHandle .memory)
  if !memory.hostVisible then throw .memoryNotHostVisible
  if memory.mapped then throw .memoryAlreadyMapped
  let memories := s.memories.map fun m => if m.handle == h then { m with mapped := true } else m
  pure ((), { s with memories := memories, audit := s.audit ++ [.memoryMapped h] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def unmapMemory (h : MemoryHandle) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .memory h
  let some memory := s.memories.find? (fun m => m.handle == h) | throw (.invalidHandle .memory)
  if !memory.mapped then throw .memoryNotMapped
  let memories := s.memories.map fun m => if m.handle == h then { m with mapped := false } else m
  pure ((), { s with memories := memories, audit := s.audit ++ [.memoryUnmapped h] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def createBuffer (bytes : Nat) : Transition BufferHandle := fun s => do
  let _ ← requireOperationalDevice s
  if s.buffers.length >= s.capability.limits.maxBuffers then throw (.poolExhausted .buffer)
  let (h, s') := freshHandle s .buffer
  let buffer : Buffer := { handle := h, bytes := bytes }
  pure (h, { s' with buffers := buffer :: s'.buffers, audit := s'.audit ++ [.bufferCreated h bytes] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def bindBufferMemory (buffer : BufferHandle) (memory : MemoryHandle) (offset : Nat) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .buffer buffer
  checkHandle s .memory memory
  let some b := s.buffers.find? (fun b => b.handle == buffer) | throw (.invalidHandle .buffer)
  let some m := s.memories.find? (fun m => m.handle == memory) | throw (.invalidHandle .memory)
  if offset > m.bytes || b.bytes > m.bytes - offset then throw .rangeOutOfBounds
  if b.binding.isSome then throw (.resourceInUse .buffer)
  let (bindingKey, s') := freshHandle s .binding
  let binding : MemorySlice := { binding := bindingKey, buffer := buffer, memory := memory, offset := offset, bytes := b.bytes }
  let buffers := s'.buffers.map fun x => if x.handle == buffer then { x with binding := some binding } else x
  pure ((), { s' with buffers := buffers, audit := s'.audit ++ [.bufferBound buffer memory offset] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def allocateDescriptor : Transition DescriptorHandle := fun s => do
  let _ ← requireOperationalDevice s
  if s.descriptors.length >= s.capability.limits.maxDescriptors then throw (.poolExhausted .descriptor)
  let (h, s') := freshHandle s .descriptor
  pure (h, { s' with descriptors := { handle := h } :: s'.descriptors })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def updateDescriptor (descriptor : DescriptorHandle) (buffer : BufferHandle) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .descriptor descriptor
  checkHandle s .buffer buffer
  let some b := s.buffers.find? (fun b => b.handle == buffer) | throw (.invalidHandle .buffer)
  if b.binding.isNone then throw (.invalidHandle .memory)
  if s.submissions.any (fun sub => sub.descriptors.contains descriptor &&
      (sub.phase == .inFlight || sub.phase == .completedButUnobserved)) then
    throw (.resourceInUse .descriptor)
  let descriptors := s.descriptors.map fun d => if d.handle == descriptor then { d with buffer := some buffer } else d
  pure ((), { s with descriptors := descriptors, audit := s.audit ++ [.descriptorUpdated descriptor buffer] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def allocateCommandBuffer : Transition CommandBufferHandle := fun s => do
  let _ ← requireOperationalDevice s
  if s.commandBuffers.length >= s.capability.limits.maxCommandBuffers then throw (.poolExhausted .commandBuffer)
  let (h, s') := freshHandle s .commandBuffer
  pure (h, { s' with commandBuffers := { handle := h } :: s'.commandBuffers })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def beginCommands (commandBuffer : CommandBufferHandle) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .commandBuffer commandBuffer
  let some cb := s.commandBuffers.find? (fun c => c.handle == commandBuffer) | throw (.invalidHandle .commandBuffer)
  if cb.state != .initial && cb.state != .executable then throw .invalidCommandState
  let commandBuffers := s.commandBuffers.map fun c =>
    if c.handle == commandBuffer then { c with state := .recording, commands := [] } else c
  pure ((), { s with commandBuffers := commandBuffers })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def recordDispatch (commandBuffer : CommandBufferHandle) (descriptor : DescriptorHandle) (x y z : Nat) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .commandBuffer commandBuffer
  checkHandle s .descriptor descriptor
  let some cb := s.commandBuffers.find? (fun c => c.handle == commandBuffer) | throw (.invalidHandle .commandBuffer)
  let some d := s.descriptors.find? (fun d => d.handle == descriptor) | throw (.invalidHandle .descriptor)
  if cb.state != .recording || d.buffer.isNone then throw .invalidCommandState
  let commandBuffers := s.commandBuffers.map fun c =>
    if c.handle == commandBuffer then { c with commands := c.commands ++ [.dispatch descriptor x y z] } else c
  pure ((), { s with commandBuffers := commandBuffers, audit := s.audit ++ [.commandRecorded commandBuffer] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def endCommands (commandBuffer : CommandBufferHandle) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .commandBuffer commandBuffer
  let some cb := s.commandBuffers.find? (fun c => c.handle == commandBuffer) | throw (.invalidHandle .commandBuffer)
  if cb.state != .recording || cb.commands.isEmpty then throw .invalidCommandState
  let commandBuffers := s.commandBuffers.map fun c => if c.handle == commandBuffer then { c with state := .executable } else c
  pure ((), { s with commandBuffers := commandBuffers })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def createFence : Transition FenceHandle := fun s => do
  let _ ← requireOperationalDevice s
  let (h, s') := freshHandle s .fence
  pure (h, { s' with fences := { handle := h } :: s'.fences })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def commandDescriptors (cb : CommandBuffer) : List DescriptorHandle :=
  cb.commands.map fun | .dispatch d _ _ _ => d

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def submit (commandBuffer : CommandBufferHandle) (fence : FenceHandle) : Transition SubmissionHandle := fun s => do
  let _ ← requireOperationalDevice s
  if !s.acceptsSubmissions then throw .cooperationCancelled
  if s.submissions.length >= s.capability.limits.maxSubmissions then throw (.poolExhausted .submission)
  checkHandle s .commandBuffer commandBuffer
  checkHandle s .fence fence
  let some cb := s.commandBuffers.find? (fun c => c.handle == commandBuffer) | throw (.invalidHandle .commandBuffer)
  let some f := s.fences.find? (fun x => x.handle == fence) | throw (.invalidHandle .fence)
  if cb.state != .executable then throw .invalidCommandState
  if f.state != .unsignaled then throw .invalidFenceState
  let descriptorHandles := commandDescriptors cb
  let bindings := descriptorHandles.filterMap fun dh => do
    let d ← s.descriptors.find? (fun d => d.handle == dh)
    let bh ← d.buffer
    let b ← s.buffers.find? (fun b => b.handle == bh)
    b.binding
  let (h, s') := freshHandle s .submission
  let submission : Submission := {
    handle := h, commandBuffer := commandBuffer, fence := fence,
    descriptors := descriptorHandles, bindings := bindings }
  let commandBuffers := s'.commandBuffers.map fun c => if c.handle == commandBuffer then { c with state := .pending } else c
  let fences := s'.fences.map fun x => if x.handle == fence then { x with state := .pending } else x
  pure (h, { s' with
    commandBuffers := commandBuffers, fences := fences,
    submissions := submission :: s'.submissions,
    audit := s'.audit ++ [.submitted h fence] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Stops new submissions but does not revoke already-submitted work. -/
def cancelCooperation : Transition Unit := fun s =>
  .ok ((), { s with acceptsSubmissions := false, audit := s.audit ++ [.cooperationStopped] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Abandoning a host wait changes no fence, submission, or resource authority. -/
def abandonWait (fence : FenceHandle) : Transition Unit := fun s => do
  checkHandle s .fence fence
  pure ((), { s with audit := s.audit ++ [.waitAbandoned fence] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- A device-agent transition, never inferred from CPU ordering. -/
def completeSubmission (submission : SubmissionHandle) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .submission submission
  let some sub := s.submissions.find? (fun x => x.handle == submission) | throw .submissionNotFound
  if sub.phase != .inFlight then throw .submissionNotFound
  let fences := s.fences.map fun f => if f.handle == sub.fence then { f with state := .signaled } else f
  let submissions := s.submissions.map fun x =>
    if x.handle == submission then { x with phase := .completedButUnobserved } else x
  pure ((), { s with fences := fences, submissions := submissions, audit := s.audit ++ [.deviceCompleted submission] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def waitFence (fence : FenceHandle) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .fence fence
  let some f := s.fences.find? (fun x => x.handle == fence) | throw (.invalidHandle .fence)
  if f.state != .signaled then throw .fenceNotReady
  let submissions := s.submissions.map fun sub =>
    if sub.fence == fence then { sub with phase := .hostReuseAllowed, hostObservations := sub.hostObservations + 1 } else sub
  let commandBuffers := s.commandBuffers.map fun cb =>
    if s.submissions.any (fun sub => sub.fence == fence && sub.commandBuffer == cb.handle)
    then { cb with state := .executable } else cb
  let granted : List AuditEvent :=
    (s.submissions.filter (fun sub => sub.fence == fence)).map (fun sub => .hostReuseGranted sub.handle)
  pure ((), { s with
    submissions := submissions
    commandBuffers := commandBuffers
    audit := s.audit ++ [.fenceObserved fence] ++ granted })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Records a range-scoped device-to-host availability consequence independently of completion. -/
def makeRangeAvailableToHost (submission : SubmissionHandle) (binding : BindingKey) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .submission submission
  let some sub := s.submissions.find? (fun x => x.handle == submission) | throw .submissionNotFound
  if sub.phase == .inFlight then throw .fenceNotReady
  let some slice := sub.bindings.find? (fun x => x.binding == binding) | throw (.invalidHandle .binding)
  let submissions := s.submissions.map fun x =>
    if x.handle == submission && !x.availableToHost.contains slice
    then { x with availableToHost := slice :: x.availableToHost } else x
  pure ((), { s with
    submissions := submissions
    audit := s.audit ++ [.rangeAvailableToHost submission slice.memory slice.offset slice.bytes] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Models the separate noncoherent host-invalidation/visibility consequence. -/
def makeRangeVisibleToHost (submission : SubmissionHandle) (binding : BindingKey) : Transition Unit := fun s => do
  let _ ← requireOperationalDevice s
  checkHandle s .submission submission
  let some sub := s.submissions.find? (fun x => x.handle == submission) | throw .submissionNotFound
  if sub.phase != .hostReuseAllowed then throw .fenceNotReady
  let some slice := sub.availableToHost.find? (fun x => x.binding == binding) | throw (.invalidHandle .binding)
  let some memory := s.memories.find? (fun m => m.handle == slice.memory) | throw (.invalidHandle .memory)
  if !memory.hostVisible || !memory.mapped then throw .memoryNotMapped
  let submissions := s.submissions.map fun x =>
    if x.handle == submission && !x.visibleToHost.contains slice
    then { x with visibleToHost := slice :: x.visibleToHost } else x
  pure ((), { s with
    submissions := submissions
    audit := s.audit ++ [.rangeVisibleToHost submission slice.memory slice.offset slice.bytes] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Retires only the correlation record after authority was returned or loss was explicitly resolved. -/
def retireSubmission (submission : SubmissionHandle) : Transition Unit := fun s => do
  checkHandle s .submission submission
  let some sub := s.submissions.find? (fun x => x.handle == submission) | throw .submissionNotFound
  if sub.phase != .hostReuseAllowed && sub.phase != .deviceLostUseRetired then throw (.resourceInUse .submission)
  let s' := { s with submissions := s.submissions.filter (fun x => x.handle != submission) }
  pure ((), retireHandle s' .submission submission.slot submission.generation)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Device loss preserves live ownership records; it does not perform cleanup. -/
def loseDevice : Transition Unit := fun s =>
  .ok ((), { s with devicePhase := .lost, acceptsSubmissions := false, audit := s.audit ++ [.deviceWasLost] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Loss-aware wait/idle disposition: lifetime-equivalent cleanup credit, never valid contents. -/
def resolveLostSubmissionForCleanup (submission : SubmissionHandle) : Transition Unit := fun s => do
  if s.devicePhase != .lost then throw .invalidCommandState
  checkHandle s .submission submission
  let some sub := s.submissions.find? (fun x => x.handle == submission) | throw .submissionNotFound
  let submissions := s.submissions.map fun x =>
    if x.handle == submission then { x with phase := .deviceLostUseRetired } else x
  let commandBuffers := s.commandBuffers.map fun cb =>
    if cb.handle == sub.commandBuffer then { cb with state := .invalidAfterDeviceLoss } else cb
  let fences := s.fences.map fun f => if f.handle == sub.fence then { f with state := .deviceLost } else f
  pure ((), { s with
    submissions := submissions
    commandBuffers := commandBuffers
    fences := fences
    audit := s.audit ++ [.lostUseRetired submission] })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
private def bufferInFlight (s : State) (buffer : BufferHandle) : Bool :=
  s.submissions.any (fun sub =>
    (sub.phase == .inFlight || sub.phase == .completedButUnobserved) &&
    sub.bindings.any (fun binding => binding.buffer == buffer))

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def destroyDescriptor (descriptor : DescriptorHandle) : Transition Unit := fun s => do
  checkHandle s .descriptor descriptor
  if s.submissions.any (fun sub =>
      (sub.phase == .inFlight || sub.phase == .completedButUnobserved) &&
      sub.descriptors.contains descriptor) then throw (.resourceInUse .descriptor)
  let s' := { s with descriptors := s.descriptors.filter (fun d => d.handle != descriptor) }
  pure ((), retireHandle s' .descriptor descriptor.slot descriptor.generation)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def destroyBuffer (buffer : BufferHandle) : Transition Unit := fun s => do
  checkHandle s .buffer buffer
  if bufferInFlight s buffer || s.descriptors.any (fun d => d.buffer == some buffer) then throw (.resourceInUse .buffer)
  let binding := (s.buffers.find? (fun b => b.handle == buffer)).bind (fun b => b.binding)
  let s' := { s with buffers := s.buffers.filter (fun b => b.handle != buffer) }
  let s' := match binding with
    | some b => retireHandle s' .binding b.binding.slot b.binding.generation
    | none => s'
  pure ((), retireHandle s' .buffer buffer.slot buffer.generation)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def destroyMemory (memory : MemoryHandle) : Transition Unit := fun s => do
  checkHandle s .memory memory
  if s.buffers.any (fun b => b.binding.any (fun slice => slice.memory == memory)) then throw (.resourceInUse .memory)
  let s' := { s with memories := s.memories.filter (fun m => m.handle != memory) }
  pure ((), retireHandle s' .memory memory.slot memory.generation)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def destroyCommandBuffer (commandBuffer : CommandBufferHandle) : Transition Unit := fun s => do
  checkHandle s .commandBuffer commandBuffer
  let some cb := s.commandBuffers.find? (fun c => c.handle == commandBuffer) | throw (.invalidHandle .commandBuffer)
  if cb.state == .pending then throw (.resourceInUse .commandBuffer)
  let s' := { s with commandBuffers := s.commandBuffers.filter (fun c => c.handle != commandBuffer) }
  pure ((), retireHandle s' .commandBuffer commandBuffer.slot commandBuffer.generation)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def destroyFence (fence : FenceHandle) : Transition Unit := fun s => do
  checkHandle s .fence fence
  let some f := s.fences.find? (fun x => x.handle == fence) | throw (.invalidHandle .fence)
  if f.state == .pending then throw (.resourceInUse .fence)
  let s' := { s with fences := s.fences.filter (fun x => x.handle != fence) }
  pure ((), retireHandle s' .fence fence.slot fence.generation)

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Device destruction is available only after every child resource obligation is discharged. -/
def destroyDevice : Transition Unit := fun s => do
  let d ← requireDeviceIdentity s
  if !(s.memories.isEmpty && s.buffers.isEmpty && s.descriptors.isEmpty &&
      s.commandBuffers.isEmpty && s.fences.isEmpty && s.submissions.isEmpty) then
    throw .cleanupObligationsRemain
  let s' := retireHandle s .device d.slot d.generation
  pure ((), { s' with device := none })

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def defaultLimits : Limits := {
  maxMemoryAllocations := 8, maxDeviceMemoryBytes := 1024 * 1024,
  maxBuffers := 16, maxDescriptors := 16, maxCommandBuffers := 8, maxSubmissions := 8 }

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def initialState (limits : Limits := defaultLimits) : State := {
  capability := { loaderAvailable := true, computeQueueAvailable := true, limits := limits } }

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
/-- Explicit resolved-backing overlap; logical handle equality is not used as an alias proof. -/
def bindingsOverlap (a b : MemorySlice) : Bool :=
  a.memory == b.memory && a.offset < b.offset + b.bytes && b.offset < a.offset + a.bytes

end Spikes.GraphicsFoundation.Vulkan
