import Mathlib

namespace Matrix

variable {K : Type*} [Field K]

/-- A `2 × 2` matrix is square-zero if its square vanishes. -/
def IsSquareZero (A : Matrix (Fin 2) (Fin 2) K) : Prop :=
  A * A = 0

/-- The trace of the square of a `2 × 2` matrix, in terms of its trace and determinant. -/
theorem trace_mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    (A * A).trace = A.trace ^ 2 - 2 * A.det := by
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two, Matrix.mul_apply]
  ring

/-- A square-zero `2 × 2` matrix has determinant zero. -/
theorem IsSquareZero.det_eq_zero {A : Matrix (Fin 2) (Fin 2) K} (h : A.IsSquareZero) : A.det = 0 := by
  have h' : A * A = 0 := h
  have := congrArg Matrix.det h'
  rw [Matrix.det_mul] at this
  simpa using this

/-- A square-zero `2 × 2` matrix has trace zero. -/
theorem IsSquareZero.trace_eq_zero {A : Matrix (Fin 2) (Fin 2) K} (h : A.IsSquareZero) :
    A.trace = 0 := by
  have h' : A * A = 0 := h
  have hd := h.det_eq_zero
  have h1 := trace_mul_self_fin_two A
  rw [h', Matrix.trace_zero, hd] at h1
  have h2 : A.trace ^ 2 = 0 := by
    calc A.trace ^ 2 = A.trace ^ 2 - 2 * 0 := by ring
      _ = 0 := h1.symm
  exact pow_eq_zero_iff (by norm_num) |>.mp h2

end Matrix
