import Mathlib.Tactic

namespace Toy

variable {n : ℕ}

/-- A frozen definition. -/
def double (k : ℕ) : ℕ := 2 * k

theorem double_add (a b : ℕ) : double (a + b) = double a + double b := by
  unfold double; ring

end Toy

namespace Other

variable {n : ℕ}

/-- The frozen theorem's statement, proved under the same short name in another namespace. -/
theorem double_pos (h : 0 < n) : 0 < Toy.double n := by
  unfold Toy.double; omega

end Other

open Other
