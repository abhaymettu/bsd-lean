import Mathlib.Tactic

/-! Control target: a statement that is false in Mathlib's environment (`default = 0` there). -/

namespace Tamper

theorem default_nat : (default : ℕ) = 1 := by
  sorry

end Tamper
