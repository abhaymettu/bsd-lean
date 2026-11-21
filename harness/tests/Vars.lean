import Mathlib.Tactic

/-! Control target: section `variable`s with instance arguments, and a frozen def that uses them. -/

namespace Vars

variable {G : Type*} [Group G] (a b : G)

/-- Conjugation of `x` by `g`. -/
def conj' (g x : G) : G := g * x * g⁻¹

theorem conj'_one : conj' 1 a = a := by
  sorry

theorem conj'_mul (g h : G) : conj' (g * h) a = conj' g (conj' h a) := by
  sorry

theorem mul_inv_rev' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end Vars
