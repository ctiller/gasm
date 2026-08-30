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

import Spikes.GraphicsFoundation.Vulkan
import Spikes.GraphicsFoundation.Window

namespace Spikes.GraphicsFoundation.Presentation

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
inductive ObjectKind where
  | swapchain | image | shader | pipeline | depth | semaphore | presentReady | frame
  deriving Repr, DecidableEq, BEq

/-- Device-child and application-correlation identities. -/
structure Handle (kind : ObjectKind) where
  device : Nat
  slot : Nat
  generation : Nat
  deriving Repr, DecidableEq, BEq

/-- A surface is instance/native-window scoped, not a device child. -/
structure SurfaceHandle where
  scope : Nat
  slot : Nat
  generation : Nat
  deriving Repr, DecidableEq, BEq

abbrev SwapchainHandle := Handle .swapchain
abbrev ImageHandle := Handle .image
abbrev ShaderHandle := Handle .shader
abbrev PipelineHandle := Handle .pipeline
abbrev DepthHandle := Handle .depth
abbrev SemaphoreHandle := Handle .semaphore
abbrev PresentReadyHandle := Handle .presentReady
abbrev FrameHandle := Handle .frame

structure Extent where
  width : Nat
  height : Nat
  deriving Repr, DecidableEq, BEq

inductive ShaderStage where
  | vertex | fragment
  deriving Repr, DecidableEq, BEq

structure InterfaceSlot where
  location : Nat
  components : Nat
  deriving Repr, DecidableEq, BEq

structure Shader where
  handle : ShaderHandle
  stage : ShaderStage
  entryPoint : String
  inputs : List InterfaceSlot
  outputs : List InterfaceSlot
  localSerializationDigest : UInt64
  deriving Repr, DecidableEq

structure Surface where
  handle : SurfaceHandle
  window : Window.WindowHandle
  lost : Bool := false
  deriving Repr, DecidableEq

structure Swapchain where
  handle : SwapchainHandle
  surface : SurfaceHandle
  extent : Extent
  imageCount : Nat
  retiredForAcquire : Bool := false
  outOfDate : Bool := false
  suboptimal : Bool := false
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Orthogonal ownership records replace a falsely total WSI phase order. -/
structure Image where
  handle : ImageHandle
  swapchain : SwapchainHandle
  index : Nat
  acquiredBy : Option FrameHandle := none
  presentationUseBy : Option FrameHandle := none
  deriving Repr, DecidableEq

structure Pipeline where
  handle : PipelineHandle
  vertex : ShaderHandle
  fragment : ShaderHandle
  colorAttachmentCount : Nat
  depthTest : Bool
  deriving Repr, DecidableEq

/-- Depth is a device attachment, never a WSI-acquired image. -/
structure DepthAttachment where
  handle : DepthHandle
  extent : Extent
  leasedBy : Option FrameHandle := none
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- One linear, frame-indexed use prevents binary semaphore event attribution from being clobbered. -/
inductive SemaphoreUse where
  | idle
  | acquireSignaled (frame : FrameHandle)
  | acquireConsumed (frame : FrameHandle)
  | renderReserved (frame : FrameHandle)
  | renderPending (frame : FrameHandle)
  | renderSignaled (frame : FrameHandle)
  | presentWaitPendingSignal (frame : FrameHandle)
  | presentWaitSignalAvailable (frame : FrameHandle)
  | presentWaitConsumed (frame : FrameHandle)
  deriving Repr, DecidableEq, BEq

structure Semaphore where
  handle : SemaphoreHandle
  use : SemaphoreUse := .idle
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Opaque local evidence to be refined by the future pinned Vulkan profile. -/
structure PresentReadyWitness where
  handle : PresentReadyHandle
  frame : FrameHandle
  image : ImageHandle
  swapchain : SwapchainHandle
  pipeline : PipelineHandle
  requiredLayoutPresent : Bool
  sameQueueFamily : Bool
  renderDependency : SemaphoreHandle
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- `FrameHandle` is correlation identity; authority lives in these explicit facts. -/
structure Frame where
  handle : FrameHandle
  swapchain : SwapchainHandle
  image : ImageHandle
  acquireSemaphore : SemaphoreHandle
  renderSemaphore : SemaphoreHandle
  pipeline : Option PipelineHandle := none
  depth : Option DepthHandle := none
  submission : Option Vulkan.SubmissionHandle := none
  imageAcquired : Bool := true
  acquireSignalConsumed : Bool := false
  renderSubmissionLease : Bool := false
  depthSubmissionLease : Bool := false
  executionComplete : Bool := false
  hostObserved : Bool := false
  presentWaitRegistered : Bool := false
  presentWaitConsumed : Bool := false
  presentRejected : Bool := false
  presentationEngineLease : Bool := false
  imageReuseCredit : Bool := false
  beginPresentObserved : Bool := false
  releasedImageAwaitingAcquireDrain : Bool := false
  deriving Repr, DecidableEq

inductive AcquireResult where
  | success (frame : FrameHandle) (image : ImageHandle)
  | suboptimal (frame : FrameHandle) (image : ImageHandle)
  | notReady | timeout | outOfDate | surfaceLost | deviceLost
  deriving Repr, DecidableEq

inductive PresentResult where
  | accepted | suboptimal | outOfDateEnqueued | surfaceLostEnqueued
  | outOfHostMemoryNotEnqueued | outOfDeviceMemoryNotEnqueued | deviceLost
  deriving Repr, DecidableEq, BEq

inductive ReleaseResult where
  | released | extensionUnavailable | deviceLost
  deriving Repr, DecidableEq, BEq

inductive Error where
  | deviceLost | wrongThread | invalidSurface | staleSurface
  | invalidHandle (kind : ObjectKind) | staleGeneration (kind : ObjectKind) | wrongParent
  | invalidExtent | unsupportedImageCount | poolExhausted (kind : ObjectKind)
  | incompatibleShaderStages | incompatibleStageInterface | invalidFrameState
  | presentReadyMissing | imageStillOwned | swapchainStillOwned | cleanupObligationsRemain
  deriving Repr, DecidableEq

inductive SwapchainCreateResult where
  | success (swapchain : SwapchainHandle)
  | failed (reason : Error)
  deriving Repr, DecidableEq

inductive AuditEvent where
  | surfaceCreated (surface : SurfaceHandle) (window : Window.WindowHandle)
  | surfaceWasLost (surface : SurfaceHandle)
  | surfaceDestroyed (surface : SurfaceHandle)
  | swapchainCreated (swapchain : SwapchainHandle) (extent : Extent)
  | oldSwapchainRetired (swapchain : SwapchainHandle)
  | imageAcquired (frame : FrameHandle) (image : ImageHandle)
  | priorPresentUseRetiredByReacquire (oldFrame : FrameHandle) (image : ImageHandle)
  | frameRecorded (frame : FrameHandle) (pipeline : PipelineHandle) (depth : DepthHandle)
  | frameSubmitted (frame : FrameHandle) (submission : Vulkan.SubmissionHandle)
  | presentWaitRegistered (frame : FrameHandle)
  | deviceExecutionComplete (frame : FrameHandle)
  | presentWaitConsumed (frame : FrameHandle)
  | hostCompletionObserved (frame : FrameHandle)
  | beginPresentObserved (frame : FrameHandle)
  | presentationUseRetired (frame : FrameHandle) (image : ImageHandle)
  | acquiredImageReleasedExt (frame : FrameHandle) (image : ImageHandle)
  | acquiredImageReleasedBySwapchainDestroy (frame : FrameHandle) (image : ImageHandle)
  | acquireSignalDrained (frame : FrameHandle) (semaphore : SemaphoreHandle)
  | frameRetired (frame : FrameHandle)
  | swapchainInvalidated (swapchain : SwapchainHandle)
  | swapchainHandleDestroyed (swapchain : SwapchainHandle)
  | presentationBackingRetired (swapchain : SwapchainHandle)
  | destroyed (kind : ObjectKind) (slot generation : Nat)
  deriving Repr, DecidableEq

structure Limits where
  maxSwapchainImages : Nat := 4
  maxShaders : Nat := 8
  maxPipelines : Nat := 4
  maxActiveFrames : Nat := 4
  deriving Repr, DecidableEq

/-- Backing may outlive the destroyed swapchain handle while presentation still owns an image. -/
structure RetiredBacking where
  swapchain : SwapchainHandle
  surface : SurfaceHandle
  images : List Image
  deriving Repr, DecidableEq

structure State where
  instanceScope : Nat
  device : Vulkan.DeviceHandle
  uiThread : Nat
  deviceLost : Bool := false
  swapchainMaintenance1 : Bool := false
  nextSlot : Nat := 1
  surfaceGenerations : List (Nat × Nat) := []
  generations : List (ObjectKind × Nat × Nat) := []
  surfaces : List Surface := []
  swapchains : List Swapchain := []
  images : List Image := []
  retiredBackings : List RetiredBacking := []
  shaders : List Shader := []
  pipelines : List Pipeline := []
  depths : List DepthAttachment := []
  semaphores : List Semaphore := []
  presentReady : List PresentReadyWitness := []
  frames : List Frame := []
  limits : Limits := {}
  audit : List AuditEvent := []
  deriving Repr, DecidableEq

abbrev Transition (α : Type) := State → Except Error (α × State)

private def currentGeneration (s : State) (kind : ObjectKind) (slot : Nat) : Option Nat :=
  (s.generations.find? (fun x => x.1 == kind && x.2.1 == slot)).map (fun x => x.2.2)

private def check (s : State) (kind : ObjectKind) (h : Handle kind) : Except Error Unit := do
  if h.device != s.device.device then throw .wrongParent
  match currentGeneration s kind h.slot with
  | none => throw (.invalidHandle kind)
  | some generation => if generation == h.generation then pure () else throw (.staleGeneration kind)

private def checkSurface (s : State) (h : SurfaceHandle) : Except Error Unit := do
  if h.scope != s.instanceScope then throw .wrongParent
  match (s.surfaceGenerations.find? (fun x => x.1 == h.slot)).map (fun x => x.2) with
  | none => throw .invalidSurface
  | some generation => if generation == h.generation then pure () else throw .staleSurface

private def operational (s : State) : Except Error Unit :=
  if s.deviceLost then .error .deviceLost else .ok ()

private def fresh (s : State) (kind : ObjectKind) : Handle kind × State :=
  let h : Handle kind := { device := s.device.device, slot := s.nextSlot, generation := 0 }
  (h, { s with nextSlot := s.nextSlot + 1, generations := (kind, h.slot, 0) :: s.generations })

private def retire (s : State) (kind : ObjectKind) (slot generation : Nat) : State :=
  { s with
    generations := s.generations.map fun x =>
      if x.1 == kind && x.2.1 == slot then (kind, slot, generation + 1) else x
    audit := s.audit ++ [.destroyed kind slot generation] }

private def retireSurfaceGeneration (s : State) (surface : SurfaceHandle) : State :=
  { s with surfaceGenerations := s.surfaceGenerations.map fun entry =>
    if entry.1 == surface.slot then (surface.slot, surface.generation + 1) else entry }

private def retirePresentReadyForFrame (s : State) (frame : FrameHandle) : State :=
  let removed := s.presentReady.filter (fun witness => witness.frame == frame)
  let s' := { s with presentReady := s.presentReady.filter (fun witness => witness.frame != frame) }
  removed.foldl (fun state witness =>
    retire state .presentReady witness.handle.slot witness.handle.generation) s'

private def consumesActiveFrameSlot (frame : Frame) : Bool :=
  frame.imageAcquired || frame.renderSubmissionLease ||
    (frame.presentWaitRegistered && !frame.presentWaitConsumed) ||
    frame.releasedImageAwaitingAcquireDrain

def initialState (instanceScope : Nat) (device : Vulkan.DeviceHandle) (uiThread : Nat) : State :=
  { instanceScope := instanceScope, device := device, uiThread := uiThread }

def createSurface (thread : Nat) (window : Window.WindowHandle) (ws : Window.State) : Transition SurfaceHandle := fun s => do
  operational s
  if thread != s.uiThread || thread != ws.uiThread then throw .wrongThread
  if !(ws.window.any (fun w => w.handle == window)) then throw .invalidSurface
  let h : SurfaceHandle := { scope := s.instanceScope, slot := s.nextSlot, generation := 0 }
  pure (h, { s with
    nextSlot := s.nextSlot + 1
    surfaceGenerations := (h.slot, 0) :: s.surfaceGenerations
    surfaces := { handle := h, window := window } :: s.surfaces
    audit := s.audit ++ [.surfaceCreated h window] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Monotone environment-owned surface-loss injection. It discharges no child obligation. -/
def loseSurface (surface : SurfaceHandle) : Transition Unit := fun s => do
  checkSurface s surface
  let surfaces := s.surfaces.map fun current =>
    if current.handle == surface then { current with lost := true } else current
  pure ((), { s with surfaces := surfaces, audit := s.audit ++ [.surfaceWasLost surface] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Surface retirement waits for live swapchains and implementation-owned backing generations. -/
def destroySurface (surface : SurfaceHandle) : Transition Unit := fun s => do
  checkSurface s surface
  if s.swapchains.any (fun swapchain => swapchain.surface == surface) ||
      s.retiredBackings.any (fun backing => backing.surface == surface) then
    throw .cleanupObligationsRemain
  let s' := { s with
    surfaces := s.surfaces.filter (fun current => current.handle != surface)
    audit := s.audit ++ [.surfaceDestroyed surface] }
  pure ((), retireSurfaceGeneration s' surface)

private def makeSwapchain (surface : SurfaceHandle) (extent : Extent) (imageCount : Nat) : Transition SwapchainHandle := fun s => do
  operational s
  checkSurface s surface
  let some sf := s.surfaces.find? (fun x => x.handle == surface) | throw .invalidSurface
  if sf.lost then throw .invalidSurface
  if extent.width == 0 || extent.height == 0 then throw .invalidExtent
  if imageCount < 2 || imageCount > s.limits.maxSwapchainImages then throw .unsupportedImageCount
  let (h, s1) := fresh s .swapchain
  let (images, s2) := (List.range imageCount).foldl (fun (acc, st) index =>
    let (ih, st') := fresh st .image
    ({ handle := ih, swapchain := h, index := index } :: acc, st')) ([], s1)
  let swapchain : Swapchain := { handle := h, surface := surface, extent := extent, imageCount := imageCount }
  pure (h, { s2 with
    swapchains := swapchain :: s2.swapchains
    images := images ++ s2.images
    audit := s2.audit ++ [.swapchainCreated h extent] })

def createSwapchain (surface : SurfaceHandle) (extent : Extent) (imageCount : Nat) : Transition SwapchainHandle :=
  makeSwapchain surface extent imageCount

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- `oldSwapchain` is retired for new acquisition before replacement creation is attempted. -/
def recreateSwapchain (old : SwapchainHandle) (surface : SurfaceHandle) (extent : Extent)
    (imageCount : Nat) : Transition SwapchainCreateResult := fun s => do
  check s .swapchain old
  let some previous := s.swapchains.find? (fun x => x.handle == old) | throw (.invalidHandle .swapchain)
  if previous.retiredForAcquire then throw .invalidFrameState
  if previous.surface != surface then throw .wrongParent
  let swapchains := s.swapchains.map fun x => if x.handle == old then { x with retiredForAcquire := true } else x
  let retired := { s with swapchains := swapchains, audit := s.audit ++ [.oldSwapchainRetired old] }
  match makeSwapchain surface extent imageCount retired with
  | .ok (freshSwapchain, next) => pure (.success freshSwapchain, next)
  | .error reason => pure (.failed reason, retired)

def createSemaphore : Transition SemaphoreHandle := fun s => do
  operational s
  let (h, s') := fresh s .semaphore
  pure (h, { s' with semaphores := { handle := h } :: s'.semaphores })

def createDepthAttachment (extent : Extent) : Transition DepthHandle := fun s => do
  operational s
  if extent.width == 0 || extent.height == 0 then throw .invalidExtent
  let (h, s') := fresh s .depth
  pure (h, { s' with depths := { handle := h, extent := extent } :: s'.depths })

def createShader (stage : ShaderStage) (entryPoint : String) (inputs outputs : List InterfaceSlot)
    (localSerializationDigest : UInt64) : Transition ShaderHandle := fun s => do
  operational s
  if s.shaders.length >= s.limits.maxShaders then throw (.poolExhausted .shader)
  let (h, s') := fresh s .shader
  let shader : Shader := {
    handle := h
    stage := stage
    entryPoint := entryPoint
    inputs := inputs
    outputs := outputs
    localSerializationDigest := localSerializationDigest }
  pure (h, { s' with shaders := shader :: s'.shaders })

private def interfaceCompatible (vertex fragment : Shader) : Bool :=
  fragment.inputs.all (fun input => vertex.outputs.contains input)

def createPipeline (vertex fragment : ShaderHandle) (depthTest : Bool) : Transition PipelineHandle := fun s => do
  operational s
  check s .shader vertex
  check s .shader fragment
  if s.pipelines.length >= s.limits.maxPipelines then throw (.poolExhausted .pipeline)
  let some vs := s.shaders.find? (fun x => x.handle == vertex) | throw (.invalidHandle .shader)
  let some fs := s.shaders.find? (fun x => x.handle == fragment) | throw (.invalidHandle .shader)
  if vs.stage != .vertex || fs.stage != .fragment then throw .incompatibleShaderStages
  if !interfaceCompatible vs fs then throw .incompatibleStageInterface
  let (h, s') := fresh s .pipeline
  let pipeline : Pipeline := {
    handle := h
    vertex := vertex
    fragment := fragment
    colorAttachmentCount := 1
    depthTest := depthTest }
  pure (h, { s' with pipelines := pipeline :: s'.pipelines })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Single-swapchain, same-queue-family acquisition. Failure outcomes return no image authority. -/
def acquireNextImage (swapchain : SwapchainHandle) (acquireSemaphore renderSemaphore : SemaphoreHandle)
    (timedOut : Bool := false) : Transition AcquireResult := fun s => do
  if s.deviceLost then return (.deviceLost, s)
  check s .swapchain swapchain
  check s .semaphore acquireSemaphore
  check s .semaphore renderSemaphore
  if acquireSemaphore == renderSemaphore then throw .invalidFrameState
  let some acquireSync := s.semaphores.find? (fun x => x.handle == acquireSemaphore)
    | throw (.invalidHandle .semaphore)
  let some renderSync := s.semaphores.find? (fun x => x.handle == renderSemaphore)
    | throw (.invalidHandle .semaphore)
  if acquireSync.use != .idle || renderSync.use != .idle then throw .invalidFrameState
  let some sc := s.swapchains.find? (fun x => x.handle == swapchain) | throw (.invalidHandle .swapchain)
  let some sf := s.surfaces.find? (fun x => x.handle == sc.surface) | throw .invalidSurface
  if sf.lost then return (.surfaceLost, s)
  if sc.retiredForAcquire || sc.outOfDate then return (.outOfDate, s)
  if timedOut then return (.timeout, s)
  let eligible (image : Image) : Bool :=
    image.swapchain == swapchain && image.acquiredBy.isNone &&
    match image.presentationUseBy with
    | none => true
    | some oldFrame => s.frames.any (fun f =>
        f.handle == oldFrame && f.executionComplete && f.presentWaitConsumed)
  let some image := s.images.find? eligible
    | pure (.notReady, s)
  if (s.frames.filter consumesActiveFrameSlot).length >= s.limits.maxActiveFrames then
    throw (.poolExhausted .frame)
  let (frame, s') := fresh s .frame
  let priorPresent := image.presentationUseBy
  let record : Frame := {
    handle := frame
    swapchain := swapchain
    image := image.handle
    acquireSemaphore := acquireSemaphore
    renderSemaphore := renderSemaphore }
  let frames := record :: s'.frames.map fun old =>
    if priorPresent == some old.handle then
      { old with presentationEngineLease := false, imageReuseCredit := true }
    else old
  let images := s'.images.map fun x => if x.handle == image.handle then
    { x with acquiredBy := some frame, presentationUseBy := none } else x
  let semaphores := s'.semaphores.map fun x =>
    if x.handle == acquireSemaphore then { x with use := .acquireSignaled frame }
    else if x.handle == renderSemaphore then { x with use := .renderReserved frame }
    else x
  let priorAudit := match priorPresent with
    | some old => [.priorPresentUseRetiredByReacquire old image.handle]
    | none => []
  let state := { s' with
    frames := frames
    images := images
    semaphores := semaphores
    audit := s'.audit ++ priorAudit ++ [.imageAcquired frame image.handle] }
  pure (if sc.suboptimal then .suboptimal frame image.handle else .success frame image.handle, state)

def recordFrame (frame : FrameHandle) (pipeline : PipelineHandle) (depth : DepthHandle) : Transition Unit := fun s => do
  operational s
  check s .frame frame
  check s .pipeline pipeline
  check s .depth depth
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  let some d := s.depths.find? (fun x => x.handle == depth) | throw (.invalidHandle .depth)
  let some sc := s.swapchains.find? (fun x => x.handle == f.swapchain) | throw (.invalidHandle .swapchain)
  if f.pipeline.isSome || f.submission.isSome || d.leasedBy.isSome || d.extent != sc.extent then throw .invalidFrameState
  let frames := s.frames.map fun x => if x.handle == frame then { x with pipeline := some pipeline, depth := some depth } else x
  pure ((), { s with frames := frames, audit := s.audit ++ [.frameRecorded frame pipeline depth] })

def declarePresentReady (frame : FrameHandle) : Transition PresentReadyHandle := fun s => do
  operational s
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if f.submission.isSome || f.presentWaitRegistered ||
      s.presentReady.any (fun witness => witness.frame == frame) then throw .invalidFrameState
  let some pipeline := f.pipeline | throw .presentReadyMissing
  let (h, s') := fresh s .presentReady
  let witness : PresentReadyWitness := {
    handle := h
    frame := frame
    image := f.image
    swapchain := f.swapchain
    pipeline := pipeline
    requiredLayoutPresent := true
    sameQueueFamily := true
    renderDependency := f.renderSemaphore }
  pure (h, { s' with presentReady := witness :: s'.presentReady })

def submitFrame (frame : FrameHandle) (submission : Vulkan.SubmissionHandle) : Transition Unit := fun s => do
  operational s
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if f.pipeline.isNone || f.depth.isNone || f.submission.isSome then throw .invalidFrameState
  let some acquire := s.semaphores.find? (fun x => x.handle == f.acquireSemaphore) | throw (.invalidHandle .semaphore)
  let some rendered := s.semaphores.find? (fun x => x.handle == f.renderSemaphore) | throw (.invalidHandle .semaphore)
  let some depth := f.depth | throw .invalidFrameState
  let some depthRecord := s.depths.find? (fun x => x.handle == depth) | throw (.invalidHandle .depth)
  if acquire.use != .acquireSignaled frame || rendered.use != .renderReserved frame ||
      depthRecord.leasedBy.isSome then throw .invalidFrameState
  let frames := s.frames.map fun x => if x.handle == frame then
    { x with
      submission := some submission
      acquireSignalConsumed := true
      renderSubmissionLease := true
      depthSubmissionLease := true } else x
  let depths := s.depths.map fun x => if f.depth == some x.handle then { x with leasedBy := some frame } else x
  let semaphores := s.semaphores.map fun x =>
    if x.handle == f.acquireSemaphore then { x with use := .acquireConsumed frame }
    else if x.handle == f.renderSemaphore then { x with use := .renderPending frame }
    else x
  pure ((), { s with
    frames := frames
    depths := depths
    semaphores := semaphores
    audit := s.audit ++ [.frameSubmitted frame submission] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Present enqueue consumes an exact opaque readiness witness but need not wait for render completion. -/
def queuePresent (frame : FrameHandle) (ready : PresentReadyHandle)
    (preEnqueueFailure : Option Bool := none) : Transition PresentResult := fun s => do
  if s.deviceLost then return (.deviceLost, s)
  check s .frame frame
  check s .presentReady ready
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  let some witness := s.presentReady.find? (fun x => x.handle == ready) | throw .presentReadyMissing
  let some pipeline := f.pipeline | throw .presentReadyMissing
  if witness.frame != frame || witness.image != f.image || witness.swapchain != f.swapchain ||
      witness.pipeline != pipeline || witness.renderDependency != f.renderSemaphore ||
      !witness.requiredLayoutPresent || !witness.sameQueueFamily || f.submission.isNone ||
      f.presentWaitRegistered then throw .presentReadyMissing
  let some renderSync := s.semaphores.find? (fun x => x.handle == f.renderSemaphore)
    | throw (.invalidHandle .semaphore)
  if renderSync.use != .renderPending frame && renderSync.use != .renderSignaled frame then
    throw .invalidFrameState
  match preEnqueueFailure with
  | some true => return (.outOfHostMemoryNotEnqueued, s)
  | some false => return (.outOfDeviceMemoryNotEnqueued, s)
  | none => pure ()
  let some sc := s.swapchains.find? (fun x => x.handle == f.swapchain) | throw (.invalidHandle .swapchain)
  let some sf := s.surfaces.find? (fun x => x.handle == sc.surface) | throw .invalidSurface
  let rejected := sf.lost || sc.outOfDate
  let frames := s.frames.map fun x => if x.handle == frame then
    { x with
      imageAcquired := false
      presentWaitRegistered := true
      presentRejected := rejected
      presentationEngineLease := !rejected } else x
  let images := s.images.map fun x => if x.handle == f.image then
    { x with acquiredBy := none, presentationUseBy := some frame } else x
  let semaphores := s.semaphores.map fun x => if x.handle == f.renderSemaphore then
    { x with use := match x.use with
      | .renderPending owner => .presentWaitPendingSignal owner
      | .renderSignaled owner => .presentWaitSignalAvailable owner
      | other => other } else x
  let s' := retire { s with
    frames := frames
    images := images
    semaphores := semaphores
    presentReady := s.presentReady.filter (fun x => x.handle != ready)
    audit := s.audit ++ [.presentWaitRegistered frame] } .presentReady ready.slot ready.generation
  let result := if sf.lost then PresentResult.surfaceLostEnqueued
    else if sc.outOfDate then PresentResult.outOfDateEnqueued
    else if sc.suboptimal then PresentResult.suboptimal else PresentResult.accepted
  pure (result, s')

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Device completion returns render/depth leases, but not presentation-engine or present-wait leases. -/
def completeFrame (frame : FrameHandle) : Transition Unit := fun s => do
  operational s
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if !f.renderSubmissionLease || f.executionComplete then throw .invalidFrameState
  let some renderSync := s.semaphores.find? (fun x => x.handle == f.renderSemaphore)
    | throw (.invalidHandle .semaphore)
  if renderSync.use != .renderPending frame && renderSync.use != .presentWaitPendingSignal frame then
    throw .invalidFrameState
  let frames := s.frames.map fun x => if x.handle == frame then
    { x with renderSubmissionLease := false, depthSubmissionLease := false, executionComplete := true } else x
  let depths := s.depths.map fun x => if x.leasedBy == some frame then { x with leasedBy := none } else x
  let semaphores := s.semaphores.map fun x => if x.handle == f.renderSemaphore then
    { x with use := match x.use with
      | .renderPending owner => .renderSignaled owner
      | .presentWaitPendingSignal owner => .presentWaitSignalAvailable owner
      | other => other } else x
  pure ((), { s with
    frames := frames
    depths := depths
    semaphores := semaphores
    audit := s.audit ++ [.deviceExecutionComplete frame] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Presentation-engine consumption is separate from render completion. -/
def consumePresentWait (frame : FrameHandle) : Transition Unit := fun s => do
  operational s
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  let some semaphore := s.semaphores.find? (fun x => x.handle == f.renderSemaphore) | throw (.invalidHandle .semaphore)
  if !f.presentWaitRegistered || !f.executionComplete ||
      semaphore.use != .presentWaitSignalAvailable frame then throw .invalidFrameState
  let frames := s.frames.map fun x => if x.handle == frame then
    { x with presentWaitConsumed := true, imageReuseCredit := x.imageReuseCredit || x.presentRejected } else x
  let images := s.images.map fun image =>
    if f.presentRejected && image.handle == f.image && image.presentationUseBy == some frame then
      { image with presentationUseBy := none }
    else image
  let semaphores := s.semaphores.map fun x => if x.handle == f.renderSemaphore then
    { x with use := .presentWaitConsumed frame } else x
  pure ((), { s with
    frames := frames
    images := images
    semaphores := semaphores
    audit := s.audit ++ [.presentWaitConsumed frame] })

def observeCompletion (frame : FrameHandle) : Transition Unit := fun s => do
  operational s
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if !f.executionComplete then throw .invalidFrameState
  let frames := s.frames.map fun x => if x.handle == frame then { x with hostObserved := true } else x
  pure ((), { s with frames := frames, audit := s.audit ++ [.hostCompletionObserved frame] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Optional begin-present observation; it grants neither completion nor reuse. -/
def observeBeginPresent (frame : FrameHandle) : Transition Unit := fun s => do
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if !f.presentWaitConsumed || !f.presentationEngineLease then throw .invalidFrameState
  let frames := s.frames.map fun x => if x.handle == frame then { x with beginPresentObserved := true } else x
  pure ((), { s with frames := frames, audit := s.audit ++ [.beginPresentObserved frame] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Selected `VK_EXT_swapchain_maintenance1` release; base KHR returns `extensionUnavailable`. -/
def releaseAcquiredImageExt (frame : FrameHandle) : Transition ReleaseResult := fun s => do
  if s.deviceLost then return (.deviceLost, s)
  if !s.swapchainMaintenance1 then return (.extensionUnavailable, s)
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if !f.imageAcquired || f.submission.isSome || f.renderSubmissionLease ||
      f.presentWaitRegistered || f.presentationEngineLease then throw .imageStillOwned
  let some acquireSync := s.semaphores.find? (fun semaphore => semaphore.handle == f.acquireSemaphore)
    | throw (.invalidHandle .semaphore)
  let some renderSync := s.semaphores.find? (fun semaphore => semaphore.handle == f.renderSemaphore)
    | throw (.invalidHandle .semaphore)
  if acquireSync.use != .acquireSignaled frame || renderSync.use != .renderReserved frame then
    throw .invalidFrameState
  let images := s.images.map fun x => if x.handle == f.image && x.acquiredBy == some frame then
    { x with acquiredBy := none } else x
  let frames := s.frames.map fun current => if current.handle == frame then
    { current with imageAcquired := false, releasedImageAwaitingAcquireDrain := true } else current
  let semaphores := s.semaphores.map fun semaphore =>
    if semaphore.handle == f.renderSemaphore then { semaphore with use := .idle } else semaphore
  let s' := { s with
    frames := frames
    images := images
    semaphores := semaphores
    audit := s.audit ++ [.acquiredImageReleasedExt frame f.image] }
  pure (.released, retirePresentReadyForFrame s' frame)

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Exact-owner wait consumes a released image's still-outstanding acquire semaphore payload. -/
def drainReleasedAcquireSignal (frame : FrameHandle) : Transition Unit := fun s => do
  check s .frame frame
  let some f := s.frames.find? (fun current => current.handle == frame) | throw (.invalidHandle .frame)
  if !f.releasedImageAwaitingAcquireDrain || f.imageAcquired || f.submission.isSome then
    throw .invalidFrameState
  let some acquireSync := s.semaphores.find? (fun semaphore => semaphore.handle == f.acquireSemaphore)
    | throw (.invalidHandle .semaphore)
  if acquireSync.use != .acquireSignaled frame then throw .invalidFrameState
  let semaphores := s.semaphores.map fun semaphore =>
    if semaphore.handle == f.acquireSemaphore then { semaphore with use := .idle } else semaphore
  let s' := { s with
    frames := s.frames.filter (fun current => current.handle != frame)
    semaphores := semaphores
    audit := s.audit ++ [.acquireSignalDrained frame f.acquireSemaphore, .frameRetired frame] }
  let s' := retirePresentReadyForFrame s' frame
  pure ((), retire s' .frame frame.slot frame.generation)

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Explicit presentation-agent completion for an exact old-generation image use. -/
def completePresentationUse (frame : FrameHandle) : Transition Unit := fun s => do
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if !f.presentationEngineLease || !f.presentWaitConsumed then throw .invalidFrameState
  let frames := s.frames.map fun x => if x.handle == frame then
    { x with presentationEngineLease := false, imageReuseCredit := true } else x
  let clearUse (image : Image) : Image :=
    if image.handle == f.image && image.presentationUseBy == some frame then
      { image with presentationUseBy := none }
    else image
  let images := s.images.map clearUse
  let retiredBackings := s.retiredBackings.map fun backing =>
    { backing with images := backing.images.map clearUse }
  pure ((), { s with
    frames := frames
    images := images
    retiredBackings := retiredBackings
    audit := s.audit ++ [.presentationUseRetired frame f.image] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Reuse requires reacquisition-derived credit; a host render fence is insufficient. -/
def retireFrame (frame : FrameHandle) : Transition Unit := fun s => do
  check s .frame frame
  let some f := s.frames.find? (fun x => x.handle == frame) | throw (.invalidHandle .frame)
  if !f.hostObserved || !f.presentWaitConsumed || !f.imageReuseCredit || f.presentationEngineLease ||
      f.renderSubmissionLease || f.depthSubmissionLease then throw .imageStillOwned
  let ownsFrame : SemaphoreUse → Bool
    | .idle => false
    | .acquireSignaled owner | .acquireConsumed owner | .renderReserved owner |
      .renderPending owner | .renderSignaled owner | .presentWaitPendingSignal owner |
      .presentWaitSignalAvailable owner | .presentWaitConsumed owner => owner == frame
  let semaphores := s.semaphores.map fun x => if ownsFrame x.use then { x with use := .idle } else x
  let s' := { s with
    frames := s.frames.filter (fun x => x.handle != frame)
    semaphores := semaphores
    audit := s.audit ++ [.frameRetired frame] }
  let s' := retirePresentReadyForFrame s' frame
  pure ((), retire s' .frame frame.slot frame.generation)

def invalidateSwapchain (swapchain : SwapchainHandle) (suboptimal : Bool := false) : Transition Unit := fun s => do
  check s .swapchain swapchain
  let swapchains := s.swapchains.map fun x => if x.handle == swapchain then
    if suboptimal then { x with suboptimal := true }
    else { x with outOfDate := true }
    else x
  pure ((), { s with swapchains := swapchains, audit := s.audit ++ [.swapchainInvalidated swapchain] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Images are implementation-owned; handle destruction transfers them to a backing-retirement ledger. -/
def destroySwapchain (swapchain : SwapchainHandle) : Transition Unit := fun s => do
  check s .swapchain swapchain
  let some swapchainRecord := s.swapchains.find? (fun current => current.handle == swapchain)
    | throw (.invalidHandle .swapchain)
  if s.frames.any (fun f => f.swapchain == swapchain &&
      (f.renderSubmissionLease || (f.presentWaitRegistered && !f.presentWaitConsumed))) then
    throw .swapchainStillOwned
  let closingFrames := s.frames.filter (fun f =>
    f.swapchain == swapchain && f.imageAcquired && f.submission.isNone && !f.presentWaitRegistered)
  if s.images.any (fun i => i.swapchain == swapchain && i.acquiredBy.any (fun owner =>
      !(closingFrames.any (fun f => f.handle == owner)))) then throw .swapchainStillOwned
  if closingFrames.any (fun frame =>
      !(s.semaphores.any (fun semaphore =>
        semaphore.handle == frame.acquireSemaphore && semaphore.use == .acquireSignaled frame.handle)) ||
      !(s.semaphores.any (fun semaphore =>
        semaphore.handle == frame.renderSemaphore && semaphore.use == .renderReserved frame.handle))) then
    throw .invalidFrameState
  let owned := s.images.filter (fun i => i.swapchain == swapchain)
    |>.map (fun i => { i with acquiredBy := none })
  let semaphores := s.semaphores.map fun sem =>
    match sem.use with
    | .renderReserved owner =>
        if closingFrames.any (fun frame => frame.handle == owner) then { sem with use := .idle } else sem
    | _ => sem
  let frames := s.frames.map fun frame =>
    if closingFrames.any (fun closing => closing.handle == frame.handle) then
      { frame with imageAcquired := false, releasedImageAwaitingAcquireDrain := true }
    else frame
  let releaseAudit := closingFrames.map fun frame =>
    .acquiredImageReleasedBySwapchainDestroy frame.handle frame.image
  let s' := { s with
    images := s.images.filter (fun i => i.swapchain != swapchain)
    swapchains := s.swapchains.filter (fun x => x.handle != swapchain)
    retiredBackings := {
      swapchain := swapchain
      surface := swapchainRecord.surface
      images := owned } :: s.retiredBackings
    frames := frames
    semaphores := semaphores
    audit := s.audit ++ releaseAudit ++ [.swapchainHandleDestroyed swapchain] }
  let s' := closingFrames.foldl (fun state frame =>
    retirePresentReadyForFrame state frame.handle) s'
  let s' := owned.foldl (fun st image => retire st .image image.handle.slot image.handle.generation) s'
  pure ((), retire s' .swapchain swapchain.slot swapchain.generation)

def retirePresentationBacking (swapchain : SwapchainHandle) : Transition Unit := fun s => do
  let some backing := s.retiredBackings.find? (fun x => x.swapchain == swapchain) | throw (.invalidHandle .swapchain)
  if backing.images.any (fun i => i.acquiredBy.isSome || i.presentationUseBy.isSome) then throw .swapchainStillOwned
  pure ((), { s with
    retiredBackings := s.retiredBackings.filter (fun x => x.swapchain != swapchain)
    audit := s.audit ++ [.presentationBackingRetired swapchain] })

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Loss preserves all unresolved image, sync, frame, and backing records. -/
def loseDevice : Transition Unit := fun s => .ok ((), { s with deviceLost := true })

end Spikes.GraphicsFoundation.Presentation
