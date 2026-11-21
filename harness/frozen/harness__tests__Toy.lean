import Mathlib.Tactic

namespace Toy

variable {n : ℕ}

/-- A frozen definition. -/
def double (k : ℕ) : ℕ := 2 * k

theorem double_add (a b : ℕ) : double (a + b) = double a + double b := by
  sorry

theorem double_pos (h : 0 < n) : 0 < double n := by
  sorry

end Toy
