/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.FormatterTextFrame

namespace Spikes.Spike2Fibonacci.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- The initial linked text word at the aligned two-digit index target is not an IAT thunk. -/
theorem spike2_initial_text_3344_not_selfref :
    spike2AfterPrologue.read64 5368713344 ≠ 5368713344 := by decide

/-- The continuation of the two-digit index formatter is ordinary text, not an IAT thunk. -/
theorem spike2_initial_text_3384_not_selfref :
    spike2AfterPrologue.read64 5368713384 ≠ 5368713384 := by decide

/-- The decimal extraction header is an ordinary text word, not a self-referential IAT slot. -/
theorem spike2_initial_text_3424_not_selfref :
    spike2AfterPrologue.read64 5368713424 ≠ 5368713424 := by decide

/-- The decimal write header is an ordinary text word, not a self-referential IAT slot. -/
theorem spike2_initial_text_3444_not_selfref :
    spike2AfterPrologue.read64 5368713444 ≠ 5368713444 := by decide

/-- The post-write CR/LF formatter boundary is an ordinary text word. -/
theorem spike2_initial_text_3457_not_selfref :
    spike2AfterPrologue.read64 5368713457 ≠ 5368713457 := by decide

end Spikes.Spike2Fibonacci.Windows
