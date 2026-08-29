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

namespace Spikes.GraphicsFoundation.Window

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
abbrev UiThreadId := Nat

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
structure ClassHandle where
  slot : Nat
  generation : Nat
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
structure WindowHandle where
  owner : UiThreadId
  slot : Nat
  generation : Nat
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
inductive MouseButton where
  | left | right | middle | x1 | x2
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
/-- Portable input meaning, independent of Win32 parameter placement. -/
inductive InputEvent where
  | keyDown (virtualKey : UInt32) (repeated : Bool)
  | keyUp (virtualKey : UInt32)
  | text (codePoint : UInt32)
  | mouseMove (x y : Int)
  | mouseButton (button : MouseButton) (pressed : Bool)
  | mouseWheel (delta : Int)
  | resized (width height : Nat)
  | focusChanged (focused : Bool)
  | closeRequested
  | destroyed
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
/-- Semantic Win32 messages; raw WPARAM/LPARAM decoding belongs to a later boundary certificate. -/
inductive Message where
  | keyDown (window : WindowHandle) (virtualKey : UInt32) (repeated : Bool)
  | keyUp (window : WindowHandle) (virtualKey : UInt32)
  | character (window : WindowHandle) (codePoint : UInt32)
  | mouseMove (window : WindowHandle) (x y : Int)
  | mouseButton (window : WindowHandle) (button : MouseButton) (pressed : Bool)
  | mouseWheel (window : WindowHandle) (delta : Int)
  | resize (window : WindowHandle) (width height : Nat)
  | focus (window : WindowHandle) (focused : Bool)
  | close (window : WindowHandle)
  | destroy (window : WindowHandle)
  | quit (exitCode : Int)
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
inductive SemanticImport where
  | registerClass | createWindow | showWindow
  | peekMessage | translateMessage | dispatchMessage | defaultWindowProc
  | destroyWindow | postQuitMessage
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
structure Requirements where
  imports : List SemanticImport := [
    .registerClass, .createWindow, .showWindow, .peekMessage, .translateMessage,
    .dispatchMessage, .defaultWindowProc, .destroyWindow, .postQuitMessage]
  acceptsKeyboard : Bool := true
  acceptsMouse : Bool := true
  acceptsResize : Bool := true
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
inductive Error where
  | loaderUnavailable
  | wrongThread
  | classAlreadyRegistered
  | classNotRegistered
  | windowAlreadyCreated
  | invalidWindow
  | staleWindow
  | noMessage
  | callbackTokenMismatch
  | callbackStillActive
  | windowStillAlive
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
structure WindowRecord where
  handle : WindowHandle
  title : String
  width : Nat
  height : Nat
  closePending : Bool := false
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
structure CallbackToken where
  owner : UiThreadId
  depth : Nat
  serial : Nat
  message : Message
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
structure State where
  loaderAvailable : Bool := true
  uiThread : UiThreadId
  windowClass : Option ClassHandle := none
  window : Option WindowRecord := none
  windowGeneration : Nat := 0
  nextSlot : Nat := 1
  nextCallbackSerial : Nat := 1
  callbackStack : List CallbackToken := []
  messages : List Message := []
  input : List InputEvent := []
  quitCode : Option Int := none
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
abbrev Transition (α : Type) := State → Except Error (α × State)

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
private def requireThread (thread : UiThreadId) (s : State) : Except Error Unit :=
  if thread == s.uiThread then .ok () else .error .wrongThread

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
private def requireWindow (h : WindowHandle) (s : State) : Except Error WindowRecord := do
  if h.owner != s.uiThread then throw .wrongThread
  if h.generation != s.windowGeneration then throw .staleWindow
  match s.window with
  | some w => if w.handle == h then pure w else throw .invalidWindow
  | none => throw .invalidWindow

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
def initialState (uiThread : UiThreadId) (loaderAvailable : Bool := true) : State := {
  loaderAvailable := loaderAvailable, uiThread := uiThread }

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
def registerClass (thread : UiThreadId) : Transition ClassHandle := fun s => do
  requireThread thread s
  if !s.loaderAvailable then throw .loaderUnavailable
  if s.windowClass.isSome then throw .classAlreadyRegistered
  let h : ClassHandle := { slot := s.nextSlot, generation := 0 }
  pure (h, { s with windowClass := some h, nextSlot := s.nextSlot + 1 })

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
def createWindow (thread : UiThreadId) (title : String) (width height : Nat) : Transition WindowHandle := fun s => do
  requireThread thread s
  if !s.loaderAvailable then throw .loaderUnavailable
  if s.windowClass.isNone then throw .classNotRegistered
  if s.window.isSome then throw .windowAlreadyCreated
  let h : WindowHandle := { owner := thread, slot := s.nextSlot, generation := s.windowGeneration }
  let w : WindowRecord := { handle := h, title := title, width := width, height := height }
  pure (h, { s with window := some w, nextSlot := s.nextSlot + 1 })

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
def postMessage (thread : UiThreadId) (message : Message) : Transition Unit := fun s => do
  requireThread thread s
  match message with
  | .quit _ => pure ((), { s with messages := s.messages ++ [message] })
  | .keyDown h _ _ | .keyUp h _ | .character h _ | .mouseMove h _ _ |
    .mouseButton h _ _ | .mouseWheel h _ | .resize h _ _ | .focus h _ |
    .close h | .destroy h =>
      let _ ← requireWindow h s
      pure ((), { s with messages := s.messages ++ [message] })

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
/-- Enters the next callback and returns a linear token. Calling this again models reentrancy. -/
def enterDispatch (thread : UiThreadId) : Transition CallbackToken := fun s => do
  requireThread thread s
  match s.messages with
  | [] => throw .noMessage
  | message :: rest =>
    let token : CallbackToken := {
      owner := thread, depth := s.callbackStack.length + 1,
      serial := s.nextCallbackSerial, message := message }
    pure (token, { s with
      messages := rest, callbackStack := token :: s.callbackStack,
      nextCallbackSerial := s.nextCallbackSerial + 1 })

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
private def eventOfMessage : Message → Option InputEvent
  | .keyDown _ key repeated => some (.keyDown key repeated)
  | .keyUp _ key => some (.keyUp key)
  | .character _ codePoint => some (.text codePoint)
  | .mouseMove _ x y => some (.mouseMove x y)
  | .mouseButton _ button pressed => some (.mouseButton button pressed)
  | .mouseWheel _ delta => some (.mouseWheel delta)
  | .resize _ width height => some (.resized width height)
  | .focus _ focused => some (.focusChanged focused)
  | .close _ => some .closeRequested
  | .destroy _ => some .destroyed
  | .quit _ => none

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
/-- Returns from exactly the top callback; nested callbacks must unwind in LIFO order. -/
def returnDispatch (thread : UiThreadId) (token : CallbackToken) : Transition Unit := fun s => do
  requireThread thread s
  match s.callbackStack with
  | [] => throw .callbackTokenMismatch
  | top :: rest =>
    if top != token then throw .callbackTokenMismatch
    let input := match eventOfMessage token.message with
      | some event => s.input ++ [event]
      | none => s.input
    let quitCode := match token.message with | .quit code => some code | _ => s.quitCode
    let window := match token.message, s.window with
      | .close h, some w => if w.handle == h then some { w with closePending := true } else some w
      | .resize h width height, some w => if w.handle == h then some { w with width := width, height := height } else some w
      | _, w => w
    pure ((), { s with callbackStack := rest, input := input, quitCode := quitCode, window := window })

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
/-- Explicit destruction is separate from receiving a close request. -/
def destroyWindow (thread : UiThreadId) (window : WindowHandle) : Transition Unit := fun s => do
  requireThread thread s
  let _ ← requireWindow window s
  if !s.callbackStack.isEmpty then throw .callbackStillActive
  pure ((), { s with
    window := none, windowGeneration := s.windowGeneration + 1,
    input := s.input ++ [.destroyed] })

/- REF: docs/GRAPHICS_FOUNDATION.md#4-window-and-input-prototype -/
def unregisterClass (thread : UiThreadId) : Transition Unit := fun s => do
  requireThread thread s
  if s.window.isSome then throw .windowStillAlive
  if !s.callbackStack.isEmpty then throw .callbackStillActive
  pure ((), { s with windowClass := none })

end Spikes.GraphicsFoundation.Window
