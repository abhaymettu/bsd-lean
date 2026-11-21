import Mathlib.Tactic

namespace Toy

variable {n : ℕ}

/-- A frozen definition. -/
def double (k : ℕ) : ℕ := 2 * k

theorem double_add (a b : ℕ) : double (a + b) = double a + double b := by
  unfold double; ring

theorem two_pos' : 0 < 2 := by native_decide

theorem double_pos (h : 0 < n) : 0 < double n := Nat.mul_pos two_pos' h

end Toy
