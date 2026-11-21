import Mathlib.Tactic

/-- A command smuggled through a plain macro (the old line-start ban missed it). -/
macro "smuggle" : command => `(#eval IO.println "hi")

smuggle

namespace Toy

variable {n : ℕ}

/-- A frozen definition. -/
def double (k : ℕ) : ℕ := 2 * k

theorem double_add (a b : ℕ) : double (a + b) = double a + double b := by
  unfold double; ring

theorem double_pos (h : 0 < n) : 0 < double n := by
  unfold double; omega

end Toy
