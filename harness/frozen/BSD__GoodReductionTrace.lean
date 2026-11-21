/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib
import BSD.GoodReduction

/-!
# Computing the trace of Frobenius from any good integral model

An admissible change of variables `(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` identifies the affine
points of `C • W` with those of `W`, over any commutative ring. Using this, we show that the number
of points of the reduction of the minimal model chosen by Mathlib equals the number of points of the
reduction of any integral model with unit discriminant. So the trace of Frobenius
`WeierstrassCurve.localTrace` can be computed from the equation one starts with.

## Main statements

* `WeierstrassCurve.Affine.equation_variableChange_iff` and
  `WeierstrassCurve.Affine.nonsingular_variableChange_iff`: a point `(x, y)` lies on `C • W` (and
  is nonsingular there) if and only if `(u²x + r, u³y + u²sx + t)` lies on `W` (and is nonsingular
  there).
* `WeierstrassCurve.Affine.natCard_point_variableChange`: `C • W` and `W` have the same number of
  affine points.
* `WeierstrassCurve.natCard_point_reduction_minimal_of_valuation_Δ_eq_one`: if `W` is integral with
  discriminant of valuation `1`, the reduction of the minimal model of `W` and the reduction of `W`
  itself have the same number of points.
* `WeierstrassCurve.localTrace_of_valuation_Δ_eq_one`: in that case the trace of Frobenius is
  `q + 1` minus the number of points of the reduction of `W` itself.
-/

namespace WeierstrassCurve

section VariableChange

variable {S : Type*} [CommRing S] (W : WeierstrassCurve S) (C : VariableChange S)

/-- A point `(x, y)` satisfies the Weierstrass equation of `C • W` if and only if
`(u²x + r, u³y + u²sx + t)` satisfies the Weierstrass equation of `W`. -/
theorem Affine.equation_variableChange_iff (x y : S) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation ((C.u : S) ^ 2 * x + C.r)
        ((C.u : S) ^ 3 * y + (C.u : S) ^ 2 * C.s * x + C.t) := by
  sorry

/-- A point `(x, y)` is a nonsingular point of `C • W` if and only if `(u²x + r, u³y + u²sx + t)`
is a nonsingular point of `W`. -/
theorem Affine.nonsingular_variableChange_iff (x y : S) :
    (C • W).toAffine.Nonsingular x y ↔
      W.toAffine.Nonsingular ((C.u : S) ^ 2 * x + C.r)
        ((C.u : S) ^ 3 * y + (C.u : S) ^ 2 * C.s * x + C.t) := by
  sorry

/-- A change of variables does not change the number of affine points. -/
theorem Affine.natCard_point_variableChange :
    Nat.card (C • W).toAffine.Point = Nat.card W.toAffine.Point := by
  sorry

end VariableChange

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K}

/-- If `W` is integral and its discriminant has valuation `1`, then the reduction of the minimal
model `W.minimal R` has as many points as the reduction of `W` itself. -/
theorem natCard_point_reduction_minimal_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) :
    Nat.card ((W.minimal R).reduction R).toAffine.Point =
      Nat.card ((W.integralModel R).map (IsLocalRing.residue R)).toAffine.Point := by
  sorry

/-- If `W` is integral and its discriminant has valuation `1`, then the trace of Frobenius is
`q + 1 - N`, where `q` is the cardinality of the residue field and `N` is the number of points of
the reduction of `W` itself. -/
theorem localTrace_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) :
    W.localTrace R = (Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
      Nat.card ((W.integralModel R).map (IsLocalRing.residue R)).toAffine.Point := by
  sorry

end WeierstrassCurve
