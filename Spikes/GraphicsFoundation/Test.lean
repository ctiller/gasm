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

import Spikes.GraphicsFoundation.Spirv
import Spikes.GraphicsFoundation.Vulkan
import Spikes.GraphicsFoundation.Window
import Spikes.GraphicsFoundation.Cube

namespace Spikes.GraphicsFoundation.Test

/- REF: docs/GRAPHICS_FOUNDATION.md#7-promotion-gates -/
def expectOk {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: expected success, got {repr error}")

/- REF: docs/GRAPHICS_FOUNDATION.md#7-promotion-gates -/
def expectError {ε α : Type} [Repr ε] [DecidableEq ε]
    (label : String) (expected : ε) : Except ε α → IO Unit
  | .error actual =>
      if actual = expected then pure ()
      else throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: expected failure, got success")

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
def testSpirv : IO Unit := do
  let scope : Spirv.ModuleScope := ⟨0xC0FFEE⟩
  let certificate ← expectOk "minimal SPIR-V certificate" (Spirv.certify (Spirv.minimalCompute scope))
  let words := Spirv.serializeWords certificate
  unless words.size > 5 && words[0]! == 0x07230203 && words[1]! == 0x00010600 do
    throw (IO.userError "SPIR-V physical header or instruction stream missing")
  let voidTy : Spirv.TypeId scope := ⟨1⟩
  let fnTy : Spirv.TypeId scope := ⟨2⟩
  let mainFn : Spirv.FunctionId scope := ⟨3⟩
  let entry : Spirv.BlockId scope := ⟨4⟩
  let missing : Spirv.BlockId scope := ⟨6⟩
  let condition : Spirv.ValueId scope := ⟨5⟩
  let malformed : Spirv.Module scope := {
    bound := 7
    instructions := [
      .capabilityShader, .memoryModelLogicalGlsl450,
      .entryPointCompute mainFn "main", .executionModeLocalSize mainFn 1 1 1,
      .typeVoid voidTy, .typeFunction fnTy voidTy [],
      .functionBegin voidTy mainFn fnTy, .label entry,
      .branchConditional condition entry missing, .functionEnd] }
  let findings := Spirv.validate malformed
  unless findings.contains .undefinedBranchTarget && findings.contains .unstructuredSelection do
    throw (IO.userError s!"SPIR-V negative control missed findings: {repr findings}")

/- REF: docs/GRAPHICS_FOUNDATION.md#3-vulkan-host-lifecycle-prototype -/
def testVulkan : IO Unit := do
  let (device, s1) ← expectOk "create device" (Vulkan.createDevice Vulkan.initialState)
  let (memory, s2) ← expectOk "allocate memory" (Vulkan.allocateMemory 4096 true s1)
  let (_, s3) ← expectOk "map memory" (Vulkan.mapMemory memory s2)
  let (buffer, s5) ← expectOk "create buffer" (Vulkan.createBuffer 1024 s3)
  let (_, s6) ← expectOk "bind buffer" (Vulkan.bindBufferMemory buffer memory 128 s5)
  let some binding := (s6.buffers.find? (fun b => b.handle == buffer)).bind (fun b => b.binding)
    | throw (IO.userError "binding capture missing")
  let (descriptor, s7) ← expectOk "allocate descriptor" (Vulkan.allocateDescriptor s6)
  let (_, s8) ← expectOk "update descriptor" (Vulkan.updateDescriptor descriptor buffer s7)
  let (commands, s9) ← expectOk "allocate command buffer" (Vulkan.allocateCommandBuffer s8)
  let (_, s10) ← expectOk "begin commands" (Vulkan.beginCommands commands s9)
  let (_, s11) ← expectOk "record dispatch" (Vulkan.recordDispatch commands descriptor 2 1 1 s10)
  let (_, s12) ← expectOk "end commands" (Vulkan.endCommands commands s11)
  let (fence, s13) ← expectOk "create fence" (Vulkan.createFence s12)
  let (submission, s14) ← expectOk "submit" (Vulkan.submit commands fence s13)
  expectError "early buffer destroy" (.resourceInUse .buffer) (Vulkan.destroyBuffer buffer s14)
  expectError "descriptor update during live submission" (.resourceInUse .descriptor)
    (Vulkan.updateDescriptor descriptor buffer s14)
  expectError "host wait before device completion" .fenceNotReady (Vulkan.waitFence fence s14)
  let (_, s15) ← expectOk "cancel cooperation" (Vulkan.cancelCooperation s14)
  let (_, s16) ← expectOk "abandon wait" (Vulkan.abandonWait fence s15)
  unless s16.submissions.length == 1 do
    throw (IO.userError "cancellation or abandoned wait revoked submitted work")
  expectError "submission after cancellation" .cooperationCancelled (Vulkan.submit commands fence s16)
  let (_, s17) ← expectOk "device completion" (Vulkan.completeSubmission submission s16)
  expectError "completion is not host reuse" (.resourceInUse .buffer) (Vulkan.destroyBuffer buffer s17)
  let (_, s18) ← expectOk "make range available" (Vulkan.makeRangeAvailableToHost submission binding.binding s17)
  let (_, s19) ← expectOk "observe fence" (Vulkan.waitFence fence s18)
  let (_, s20) ← expectOk "repeatably observe signaled fence" (Vulkan.waitFence fence s19)
  let (_, s21) ← expectOk "make range visible" (Vulkan.makeRangeVisibleToHost submission binding.binding s20)
  let some completed := s21.submissions.find? (fun sub => sub.handle == submission)
    | throw (IO.userError "completion correlation record was erased before retirement")
  unless completed.phase == .hostReuseAllowed && completed.hostObservations == 2 &&
      completed.availableToHost.contains binding && completed.visibleToHost.contains binding &&
      s21.fences.any (fun f => f.handle == fence && f.state == .signaled) do
    throw (IO.userError "completion/observation/reuse/visibility facts were conflated")
  let (_, s22) ← expectOk "retire submission correlation" (Vulkan.retireSubmission submission s21)
  let (_, s23) ← expectOk "destroy descriptor" (Vulkan.destroyDescriptor descriptor s22)
  expectError "stale descriptor generation" (.staleGeneration .descriptor) (Vulkan.destroyDescriptor descriptor s23)
  let (_, s24) ← expectOk "destroy buffer" (Vulkan.destroyBuffer buffer s23)
  let (_, s25) ← expectOk "unmap memory" (Vulkan.unmapMemory memory s24)
  let (_, s26) ← expectOk "destroy memory" (Vulkan.destroyMemory memory s25)
  let (_, s27) ← expectOk "destroy command buffer" (Vulkan.destroyCommandBuffer commands s26)
  let (_, s28) ← expectOk "destroy fence" (Vulkan.destroyFence fence s27)
  let (_, s29) ← expectOk "destroy device" (Vulkan.destroyDevice s28)
  unless s29.device.isNone && s29.audit.contains (.deviceCreated device) do
    throw (IO.userError "Vulkan cleanup or audit trail incomplete")

  -- Re-run the same immutable submitted state down the device-loss branch. Loss itself preserves
  -- every lease; only the explicit loss-aware disposition retires this exact submission for cleanup.
  let (_, lost0) ← expectOk "lose device with work in flight" (Vulkan.loseDevice s14)
  expectError "ordinary fence wait after loss" .deviceLost (Vulkan.waitFence fence lost0)
  expectError "loss alone does not release descriptor" (.resourceInUse .descriptor)
    (Vulkan.destroyDescriptor descriptor lost0)
  let (_, lost1) ← expectOk "resolve one lost submission" (Vulkan.resolveLostSubmissionForCleanup submission lost0)
  let (_, lost2) ← expectOk "retire loss correlation" (Vulkan.retireSubmission submission lost1)
  let (_, lost3) ← expectOk "destroy descriptor after loss disposition" (Vulkan.destroyDescriptor descriptor lost2)
  let (_, lost4) ← expectOk "destroy buffer after loss disposition" (Vulkan.destroyBuffer buffer lost3)
  let (_, lost5) ← expectOk "free backing after loss disposition" (Vulkan.destroyMemory memory lost4)
  let (_, lost6) ← expectOk "destroy invalidated command buffer" (Vulkan.destroyCommandBuffer commands lost5)
  let (_, lost7) ← expectOk "destroy loss fence" (Vulkan.destroyFence fence lost6)
  let (_, lost8) ← expectOk "destroy lost device" (Vulkan.destroyDevice lost7)
  unless lost8.device.isNone do throw (IO.userError "loss-aware submission cleanup did not close")

  let (_, loss1) ← expectOk "loss control create device" (Vulkan.createDevice Vulkan.initialState)
  let (lossMemory, loss2) ← expectOk "loss control allocate" (Vulkan.allocateMemory 64 false loss1)
  let (_, loss3) ← expectOk "lose device" (Vulkan.loseDevice loss2)
  unless loss3.devicePhase == .lost && loss3.memories.any (fun m => m.handle == lossMemory) do
    throw (IO.userError "device loss silently erased live ownership")
  let (_, loss4) ← expectOk "free after device loss" (Vulkan.destroyMemory lossMemory loss3)
  let (_, loss5) ← expectOk "destroy lost device after cleanup" (Vulkan.destroyDevice loss4)
  unless loss5.device.isNone do throw (IO.userError "device-loss cleanup remained impossible")

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
def testWindow : IO Unit := do
  let thread := 7
  let (_, s1) ← expectOk "register class" (Window.registerClass thread (Window.initialState thread))
  let (window, s2) ← expectOk "create window" (Window.createWindow thread "gasm" 800 500 s1)
  expectError "thread affinity" .wrongThread (Window.postMessage (thread + 1) (.close window) s2)
  let (_, s3) ← expectOk "post key" (Window.postMessage thread (.keyDown window 65 false) s2)
  let (_, s4) ← expectOk "post close" (Window.postMessage thread (.close window) s3)
  let (outer, s5) ← expectOk "enter outer callback" (Window.enterDispatch thread s4)
  let (inner, s6) ← expectOk "enter reentrant callback" (Window.enterDispatch thread s5)
  expectError "destroy during callback" .callbackStillActive (Window.destroyWindow thread window s6)
  let (_, s7) ← expectOk "return inner callback" (Window.returnDispatch thread inner s6)
  let (_, s8) ← expectOk "return outer callback" (Window.returnDispatch thread outer s7)
  unless s8.window.any (fun w => w.closePending) && s8.input == [.closeRequested, .keyDown 65 false] do
    throw (IO.userError s!"window reentrancy/close trace mismatch: {repr s8.input}")
  let (_, s9) ← expectOk "destroy window" (Window.destroyWindow thread window s8)
  expectError "stale window handle" .staleWindow (Window.postMessage thread (.close window) s9)
  let (_, s10) ← expectOk "post quit" (Window.postMessage thread (.quit 0) s9)
  let (quitToken, s11) ← expectOk "enter quit" (Window.enterDispatch thread s10)
  let (_, s12) ← expectOk "return quit" (Window.returnDispatch thread quitToken s11)
  let (_, s13) ← expectOk "unregister class" (Window.unregisterClass thread s12)
  unless s13.quitCode == some 0 && s13.windowClass.isNone do
    throw (IO.userError "window teardown or quit handling incomplete")

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
def testCubePresentationClosure (surface : Presentation.SurfaceHandle)
    (swapchain : Presentation.SwapchainHandle) (frame : Presentation.FrameHandle)
    (image : Presentation.ImageHandle) (ps17 : Presentation.State) : IO Unit := do
  -- Old-generation presentation can close after handle destruction through an explicit
  -- presentation-agent event; render-fence observation alone cannot retire the backing.
  let oldImageHandles := (ps17.images.filter (fun i => i.swapchain == swapchain)).map (fun i => i.handle)
  let (_, oldClosed0) ← expectOk "destroy swapchain after queued waits complete"
    (Presentation.destroySwapchain swapchain ps17)
  unless oldImageHandles.all (fun imageHandle => oldClosed0.generations.contains
      (.image, imageHandle.slot, imageHandle.generation + 1)) do
    throw (IO.userError "swapchain destruction did not retire every image generation")
  expectError "engine-owned old backing cannot retire early" Presentation.Error.swapchainStillOwned
    (Presentation.retirePresentationBacking swapchain oldClosed0)
  let (_, oldClosed1) ← expectOk "explicitly retire old-generation presentation use"
    (Presentation.completePresentationUse frame oldClosed0)
  let (_, oldClosed2) ← expectOk "retire old-generation frame correlation"
    (Presentation.retireFrame frame oldClosed1)
  let (_, oldClosed3) ← expectOk "retire old-generation implementation backing"
    (Presentation.retirePresentationBacking swapchain oldClosed2)
  unless oldClosed3.retiredBackings.isEmpty do
    throw (IO.userError "old-generation presentation backing could not close")

  let tightCapacity := { ps17 with limits := { ps17.limits with maxActiveFrames := 1 } }
  let (acquire2, ps18) ← expectOk "create next acquire semaphore" (Presentation.createSemaphore tightCapacity)
  let (rendered2, ps19) ← expectOk "create next render semaphore" (Presentation.createSemaphore ps18)
  let reacquired ← expectOk "reacquire exact image for reuse credit"
    (Presentation.acquireNextImage swapchain acquire2 rendered2 false ps19)
  let (.success nextFrame sameImage, ps20) := reacquired
    | throw (IO.userError "same image was not reacquired")
  unless sameImage == image do throw (IO.userError "reacquisition did not retire the exact prior present use")
  unless ps20.frames.length > ps20.limits.maxActiveFrames do
    throw (IO.userError "dormant presentation correlation still consumed active-frame capacity")
  let (_, ps21) ← expectOk "retire prior frame after reacquisition" (Presentation.retireFrame frame ps20)
  let (baseRelease, baseReleaseState) ← expectOk "base KHR cannot release acquired image"
    (Presentation.releaseAcquiredImageExt nextFrame ps21)
  unless baseRelease == Presentation.ReleaseResult.extensionUnavailable && baseReleaseState == ps21 do
    throw (IO.userError "base KHR silently released an acquired image")
  let maintenanceState := { ps21 with swapchainMaintenance1 := true }
  let (extRelease, ps22) ← expectOk "maintenance1 releases acquired image"
    (Presentation.releaseAcquiredImageExt nextFrame maintenanceState)
  unless extRelease == Presentation.ReleaseResult.released do
    throw (IO.userError "maintenance1 acquired-image release did not succeed")
  expectError "released image does not make acquire semaphore reusable"
    Presentation.Error.invalidFrameState
    (Presentation.acquireNextImage swapchain acquire2 rendered2 false ps22)
  let (_, ps22Drained) ← expectOk "drain released acquire signal"
    (Presentation.drainReleasedAcquireSignal nextFrame ps22)
  let (replacement, ps23) ← expectOk "failed recreation still retires old swapchain"
    (Presentation.recreateSwapchain swapchain surface { width := 0, height := 600 } 3 ps22Drained)
  unless replacement == Presentation.SwapchainCreateResult.failed Presentation.Error.invalidExtent do
    throw (IO.userError "recreation failure was not result-indexed")
  let (acquireAfterRetire, ps24) ← expectOk "retired old swapchain rejects acquisition"
    (Presentation.acquireNextImage swapchain acquire2 rendered2 false ps23)
  unless acquireAfterRetire == Presentation.AcquireResult.outOfDate do
    throw (IO.userError "swapchain invalidation was not explicit")
  let (_, ps25) ← expectOk "destroy idle old swapchain handle" (Presentation.destroySwapchain swapchain ps24)
  expectError "stale swapchain generation" (Presentation.Error.staleGeneration .swapchain)
    (Presentation.destroySwapchain swapchain ps25)
  let (_, ps26) ← expectOk "retire implementation-owned presentation backing"
    (Presentation.retirePresentationBacking swapchain ps25)
  unless ps26.retiredBackings.isEmpty do throw (IO.userError "presentation backing ledger remained live")
  let (_, ps27) ← expectOk "orderly surface retirement" (Presentation.destroySurface surface ps26)
  expectError "retired surface generation is stale" Presentation.Error.staleSurface
    (Presentation.loseSurface surface ps27)
  let forgedSuccessor := { surface with generation := surface.generation + 1 }
  expectError "never-issued surface successor is not live" Presentation.Error.invalidSurface
    (Presentation.loseSurface forgedSuccessor ps27)

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
def testCubePresentation : IO Unit := do
  unless Cube.geometryValid && Cube.shaderContractValid Cube.shaderContract do
    throw (IO.userError "cube geometry or stage contract invalid")
  let uiThread := 11
  let (_, ws1) ← expectOk "cube register class" (Window.registerClass uiThread (Window.initialState uiThread))
  let (window, ws2) ← expectOk "cube create window" (Window.createWindow uiThread "gasm cube" 800 600 ws1)
  let (device, _) ← expectOk "cube create Vulkan device" (Vulkan.createDevice Vulkan.initialState)
  let ps0 := Presentation.initialState 0x1A57 device uiThread
  let (surface, ps1) ← expectOk "create surface" (Presentation.createSurface uiThread window ws2 ps0)
  let (swapchain, ps2) ← expectOk "create swapchain"
    (Presentation.createSwapchain surface { width := 800, height := 600 } 3 ps1)
  let (acquire, ps3) ← expectOk "create acquire semaphore" (Presentation.createSemaphore ps2)
  let (rendered, ps4) ← expectOk "create render semaphore" (Presentation.createSemaphore ps3)
  let (_, surfaceLost0) ← expectOk "environment reports monotone surface loss"
    (Presentation.loseSurface surface ps4)
  let (surfaceAcquireResult, _) ← expectOk "surface loss is reachable through transition API"
    (Presentation.acquireNextImage swapchain acquire rendered false surfaceLost0)
  unless surfaceAcquireResult == Presentation.AcquireResult.surfaceLost do
    throw (IO.userError "named surface-loss transition did not reach acquisition outcome")
  expectError "surface with live swapchain cannot retire" Presentation.Error.cleanupObligationsRemain
    (Presentation.destroySurface surface surfaceLost0)
  let (vs, ps5) ← expectOk "create vertex shader"
    (Presentation.createShader .vertex "main" Cube.shaderContract.vertexInputs
      Cube.shaderContract.vertexOutputs 0xA11CE ps4)
  let (fs, ps6) ← expectOk "create fragment shader"
    (Presentation.createShader .fragment "main" Cube.shaderContract.fragmentInputs
      Cube.shaderContract.fragmentOutputs 0xB0B ps5)
  let (pipeline, ps7) ← expectOk "create graphics pipeline" (Presentation.createPipeline vs fs true ps6)
  let (depth, ps8) ← expectOk "create depth attachment"
    (Presentation.createDepthAttachment { width := 800, height := 600 } ps7)
  let acquired ← expectOk "acquire image" (Presentation.acquireNextImage swapchain acquire rendered false ps8)
  let (.success frame image, ps9) := acquired
    | throw (IO.userError "fresh swapchain did not acquire")
  let fakeSubmission : Vulkan.SubmissionHandle := { device := device.device, slot := 900, generation := 0 }

  -- Binary semaphore roles are distinct, idle at bind, and retain exact frame attribution.
  expectError "same semaphore cannot serve acquire and render roles" Presentation.Error.invalidFrameState
    (Presentation.acquireNextImage swapchain acquire acquire false ps8)
  let (busyRender, busy0) ← expectOk "busy-semaphore control render sync" (Presentation.createSemaphore ps9)
  expectError "busy acquire semaphore cannot be rebound" Presentation.Error.invalidFrameState
    (Presentation.acquireNextImage swapchain acquire busyRender false busy0)

  -- Parent destruction releases dormant image authority but preserves the exact acquire payload.
  let (_, parent0) ← expectOk "destroy parent with unsubmitted acquired frame"
    (Presentation.destroySwapchain swapchain ps9)
  let (replacementSwapchain, parent1) ← expectOk "create replacement after parent destruction"
    (Presentation.createSwapchain surface { width := 800, height := 600 } 3 parent0)
  expectError "parent destruction cannot immediately reuse acquire semaphore"
    Presentation.Error.invalidFrameState
    (Presentation.acquireNextImage replacementSwapchain acquire rendered false parent1)
  expectError "parent-released frame cannot be recorded"
    Presentation.Error.invalidFrameState
    (Presentation.recordFrame frame pipeline depth parent1)
  expectError "parent-released frame cannot mint readiness"
    Presentation.Error.invalidFrameState
    (Presentation.declarePresentReady frame parent1)
  let (_, parentLost) ← expectOk "lose device with parent-released acquire payload"
    (Presentation.loseDevice parent1)
  expectError "device loss cannot invent parent-release drain completion"
    Presentation.Error.deviceLost
    (Presentation.drainReleasedAcquireSignal frame parentLost)
  let (_, parent2) ← expectOk "drain parent-released acquire signal"
    (Presentation.drainReleasedAcquireSignal frame parent1)
  let (parentAcquireResult, _) ← expectOk "reuse acquire semaphore after exact drain"
    (Presentation.acquireNextImage replacementSwapchain acquire rendered false parent2)
  unless match parentAcquireResult with | .success _ _ | .suboptimal _ _ => true | _ => false do
    throw (IO.userError "drained acquire semaphore did not become reusable")

  -- Two recorded frames may name one depth attachment, but only one submission can lease it.
  let (depthAcquire2, depth0) ← expectOk "depth control acquire sync" (Presentation.createSemaphore ps9)
  let (depthRender2, depth1) ← expectOk "depth control render sync" (Presentation.createSemaphore depth0)
  let depthAcquired ← expectOk "depth control second image"
    (Presentation.acquireNextImage swapchain depthAcquire2 depthRender2 false depth1)
  let (.success depthFrame2 _depthImage2, depth2) := depthAcquired
    | throw (IO.userError "depth control could not acquire second image")
  let (_, depth3) ← expectOk "record first shared-depth frame"
    (Presentation.recordFrame frame pipeline depth depth2)
  let (_, depth4) ← expectOk "record second shared-depth frame"
    (Presentation.recordFrame depthFrame2 pipeline depth depth3)
  let (_, depth5) ← expectOk "submit first shared-depth frame"
    (Presentation.submitFrame frame fakeSubmission depth4)
  let fakeSubmission2 : Vulkan.SubmissionHandle := { device := device.device, slot := 901, generation := 0 }
  expectError "second submission cannot overwrite depth lease" Presentation.Error.invalidFrameState
    (Presentation.submitFrame depthFrame2 fakeSubmission2 depth5)

  -- Saturate the other two images, then prove queued-but-incomplete F1 cannot be reacquired.
  let (blockAcquire2, block0) ← expectOk "early-reacquire blocker acquire 2" (Presentation.createSemaphore ps9)
  let (blockRender2, block1) ← expectOk "early-reacquire blocker render 2" (Presentation.createSemaphore block0)
  let blockResult2 ← expectOk "early-reacquire occupy image 2"
    (Presentation.acquireNextImage swapchain blockAcquire2 blockRender2 false block1)
  let (.success _blockFrame2 _blockImage2, block2) := blockResult2
    | throw (IO.userError "could not occupy second swapchain image")
  let (blockAcquire3, block3) ← expectOk "early-reacquire blocker acquire 3" (Presentation.createSemaphore block2)
  let (blockRender3, block4) ← expectOk "early-reacquire blocker render 3" (Presentation.createSemaphore block3)
  let blockResult3 ← expectOk "early-reacquire occupy image 3"
    (Presentation.acquireNextImage swapchain blockAcquire3 blockRender3 false block4)
  let (.success _blockFrame3 _blockImage3, block5) := blockResult3
    | throw (IO.userError "could not occupy third swapchain image")
  let (_, block6) ← expectOk "early-reacquire record F1"
    (Presentation.recordFrame frame pipeline depth block5)
  let (blockReady, block7) ← expectOk "early-reacquire readiness" (Presentation.declarePresentReady frame block6)
  let (_, block8) ← expectOk "early-reacquire submit F1" (Presentation.submitFrame frame fakeSubmission block7)
  let (_, block9) ← expectOk "early-reacquire queue F1"
    (Presentation.queuePresent frame blockReady none block8)
  let (probeAcquire, block10) ← expectOk "early-reacquire probe acquire sync" (Presentation.createSemaphore block9)
  let (probeRender, block11) ← expectOk "early-reacquire probe render sync" (Presentation.createSemaphore block10)
  let (earlyReacquire, _) ← expectOk "early-reacquire must not return F1"
    (Presentation.acquireNextImage swapchain probeAcquire probeRender false block11)
  unless earlyReacquire == Presentation.AcquireResult.notReady do
    throw (IO.userError "image was reacquired while its prior render/wait remained incomplete")

  let (_, ps10) ← expectOk "record cube frame" (Presentation.recordFrame frame pipeline depth ps9)
  let (ready, ps11) ← expectOk "declare exact present-ready witness" (Presentation.declarePresentReady frame ps10)
  expectError "duplicate present-ready witness" Presentation.Error.invalidFrameState
    (Presentation.declarePresentReady frame ps11)
  let witnessReleaseState := { ps11 with swapchainMaintenance1 := true }
  let (witnessRelease, witnessReleased) ← expectOk "release frame with unused readiness witness"
    (Presentation.releaseAcquiredImageExt frame witnessReleaseState)
  unless witnessRelease == Presentation.ReleaseResult.released &&
      witnessReleased.generations.contains
        (.presentReady, ready.slot, ready.generation + 1) do
    throw (IO.userError "filtered present-ready witness generation was not retired")
  expectError "released image cannot mint a new present-ready witness"
    Presentation.Error.invalidFrameState
    (Presentation.declarePresentReady frame witnessReleased)
  let (_, witnessLost) ← expectOk "lose device with maintenance-release acquire payload"
    (Presentation.loseDevice witnessReleased)
  expectError "device loss cannot invent maintenance-release drain completion"
    Presentation.Error.deviceLost
    (Presentation.drainReleasedAcquireSignal frame witnessLost)
  let (_, _witnessDrained) ← expectOk "drain witness-release acquire signal"
    (Presentation.drainReleasedAcquireSignal frame witnessReleased)
  let (_, ps12) ← expectOk "submit cube frame" (Presentation.submitFrame frame fakeSubmission ps11)
  expectError "post-submit present-ready witness" Presentation.Error.invalidFrameState
    (Presentation.declarePresentReady frame ps12)

  -- Pre-enqueue allocation failure is no-effect and does not consume the one-shot witness.
  let (oomResult, oomState) ← expectOk "present OOM before enqueue"
    (Presentation.queuePresent frame ready (some true) ps12)
  unless oomResult == Presentation.PresentResult.outOfHostMemoryNotEnqueued && oomState == ps12 do
    throw (IO.userError "pre-enqueue present failure changed ownership")

  -- OUT_OF_DATE still enqueues the exact semaphore wait and releases acquisition only when consumed.
  let (_, rejected0) ← expectOk "mark swapchain out of date"
    (Presentation.invalidateSwapchain swapchain false ps12)
  let (_, rejectedMonotone) ← expectOk "suboptimal cannot revive out-of-date"
    (Presentation.invalidateSwapchain swapchain true rejected0)
  unless rejectedMonotone.swapchains.any (fun sc => sc.handle == swapchain && sc.outOfDate) do
    throw (IO.userError "suboptimal transition revived an out-of-date swapchain")
  let (rejectedResult, rejected1) ← expectOk "enqueue rejected out-of-date present"
    (Presentation.queuePresent frame ready none rejectedMonotone)
  unless rejectedResult == Presentation.PresentResult.outOfDateEnqueued do
    throw (IO.userError "out-of-date present was not classified as enqueued")
  expectError "queued rejected wait blocks swapchain destruction" Presentation.Error.swapchainStillOwned
    (Presentation.destroySwapchain swapchain rejected1)
  let (_, rejected2) ← expectOk "complete rejected present render" (Presentation.completeFrame frame rejected1)
  let (_, rejected3) ← expectOk "observe rejected present render" (Presentation.observeCompletion frame rejected2)
  let (_, rejected4) ← expectOk "consume rejected present wait" (Presentation.consumePresentWait frame rejected3)
  let (_, _rejected5) ← expectOk "retire rejected present frame without engine lease"
    (Presentation.retireFrame frame rejected4)

  let (_, surfaceRejected0) ← expectOk "lose surface before present enqueue"
    (Presentation.loseSurface surface ps12)
  let (surfaceRejectedResult, surfaceRejected1) ← expectOk "enqueue surface-lost present"
    (Presentation.queuePresent frame ready none surfaceRejected0)
  unless surfaceRejectedResult == Presentation.PresentResult.surfaceLostEnqueued do
    throw (IO.userError "surface-lost present was not classified as enqueued")
  let (_, surfaceRejected2) ← expectOk "complete surface-lost render"
    (Presentation.completeFrame frame surfaceRejected1)
  let (_, surfaceRejected3) ← expectOk "observe surface-lost render"
    (Presentation.observeCompletion frame surfaceRejected2)
  let (_, surfaceRejected4) ← expectOk "consume surface-lost wait"
    (Presentation.consumePresentWait frame surfaceRejected3)
  let (_, _surfaceRejected5) ← expectOk "retire surface-lost rejected frame"
    (Presentation.retireFrame frame surfaceRejected4)

  let (presentResult, ps13) ← expectOk "queue present before completion"
    (Presentation.queuePresent frame ready none ps12)
  unless presentResult == Presentation.PresentResult.accepted do
    throw (IO.userError "presentation was not accepted")
  expectError "present acceptance is not begin-present" Presentation.Error.invalidFrameState
    (Presentation.observeBeginPresent frame ps13)
  let (_, ps14) ← expectOk "objective frame completion" (Presentation.completeFrame frame ps13)
  expectError "render completion is not present retirement" Presentation.Error.imageStillOwned
    (Presentation.retireFrame frame ps14)
  let (_, ps15) ← expectOk "host observes completion" (Presentation.observeCompletion frame ps14)
  let (_, ps16) ← expectOk "presentation consumes semaphore wait" (Presentation.consumePresentWait frame ps15)
  let (_, ps17) ← expectOk "optional begin-present observation" (Presentation.observeBeginPresent frame ps16)
  expectError "host fence and begin-present do not grant reuse" Presentation.Error.imageStillOwned
    (Presentation.retireFrame frame ps17)
  testCubePresentationClosure surface swapchain frame image ps17

/- REF: docs/GRAPHICS_FOUNDATION.md#7-promotion-gates -/
def runAll : IO UInt32 := do
  testSpirv
  IO.println "[+] SPIR-V local serialization/structural controls passed"
  testVulkan
  IO.println "[+] Vulkan lifecycle/authority/failure controls passed"
  testWindow
  IO.println "[+] Win32 window/input/reentrancy controls passed"
  testCubePresentation
  IO.println "[+] Cube geometry/pipeline/swapchain/frame controls passed"
  IO.println "[+] Graphics foundation prototype tests passed (nonnormative; no verified artifact authority)"
  pure 0

end Spikes.GraphicsFoundation.Test

/- REF: docs/GRAPHICS_FOUNDATION.md#7-promotion-gates -/
def main : IO UInt32 :=
  Spikes.GraphicsFoundation.Test.runAll
