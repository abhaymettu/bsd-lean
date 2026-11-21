import Mathlib

/-!
# Square-zero `2 × 2` matrices

A matrix `A` is square-zero if `A * A = 0`. For `2 × 2` matrices over a field this forces both the
determinant and the trace to vanish. The key identity is `tr (A * A) = tr A ^ 2 - 2 * det A`, valid over
any commutative ring.

This file is the generality example of the proof harness (`harness/prove.py`): linear algebra, not
number theory.
-/

namespace Matrix

variable {K : Type*} [Field K]

/-- A `2 × 2` matrix is square-zero if its square vanishes. -/
def IsSquareZero (A : Matrix (Fin 2) (Fin 2) K) : Prop :=
  A * A = 0

/-- The trace of the square of a `2 × 2` matrix, in terms of its trace and determinant. -/
theorem trace_mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    (A * A).trace = A.trace ^ 2 - 2 * A.det := by
  sorry

/-- A square-zero `2 × 2` matrix has determinant zero. -/
theorem IsSquareZero.det_eq_zero {A : Matrix (Fin 2) (Fin 2) K} (h : A.IsSquareZero) : A.det = 0 := by
  sorry

/-- A square-zero `2 × 2` matrix has trace zero. -/
theorem IsSquareZero.trace_eq_zero {A : Matrix (Fin 2) (Fin 2) K} (h : A.IsSquareZero) :
    A.trace = 0 := by
  sorry

end Matrix
