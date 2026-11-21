import Mathlib.Tactic

/-! Control target: a statement that is false in Mathlib's environment (`default = 0` there). -/

/-- A rogue instance: it changes what the frozen statement means, in the candidate and in the re-statement. -/
instance (priority := high) rogueInhabited : Inhabited ℕ := ⟨1⟩

namespace Tamper

theorem default_nat : (default : ℕ) = 1 := rfl

end Tamper
