/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib
import BSD.LocalFactor

/-!
# A good reduction criterion for minimal Weierstrass equations

Let `R` be a discrete valuation ring with fraction field `K` and let `W` be a Weierstrass curve over
`K`. Mathlib picks a minimal Weierstrass equation `WeierstrassCurve.minimal R W` by choice, and the
reduction type of `W` (for instance in `WeierstrassCurve.localPolynomial`) is read off this chosen
model. This file shows that the choice does not matter for good reduction: an integral Weierstrass
equation whose discriminant is a unit is minimal and has good reduction, and the chosen minimal model
of `W` has good reduction as soon as some integral model of `W` has unit discriminant.

## Main statements

* `WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one`: an integral Weierstrass equation whose
  discriminant has valuation `1` is minimal.
* `WeierstrassCurve.hasGoodReduction_of_valuation_Δ_eq_one`: such an equation has good reduction.
* `WeierstrassCurve.hasGoodReduction_minimal_of_valuation_Δ_eq_one`: if `W` is integral with
  discriminant of valuation `1`, then the chosen minimal model `W.minimal R` has good reduction.
* `WeierstrassCurve.hasGoodReduction_minimal_iff`: the chosen minimal model has good reduction if
  and only if some integral model of `W` has discriminant of valuation `1`.
* `WeierstrassCurve.localPolynomial_of_valuation_Δ_eq_one`: in that case the local polynomial of `W`
  is `1 - a T + q T ^ 2`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, minimal weierstrass equation, good reduction
-/

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum Polynomial

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K}

/-- An integral Weierstrass equation whose discriminant has valuation `1` is minimal. -/
theorem isMinimal_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  sorry

/-- An integral Weierstrass equation whose discriminant has valuation `1` has good reduction. -/
theorem hasGoodReduction_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) : HasGoodReduction R W := by
  sorry

/-- If `W` is integral and its discriminant has valuation `1`, then the minimal model
`W.minimal R` chosen by Mathlib has good reduction. -/
theorem hasGoodReduction_minimal_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) : (W.minimal R).HasGoodReduction R := by
  sorry

/-- The minimal model `W.minimal R` has good reduction if and only if some integral model of `W`
has discriminant of valuation `1`. -/
theorem hasGoodReduction_minimal_iff :
    (W.minimal R).HasGoodReduction R ↔
      ∃ C : VariableChange K, IsIntegral R (C • W) ∧ valuation K (maximalIdeal R) (C • W).Δ = 1 := by
  sorry

/-- If `W` is integral and its discriminant has valuation `1`, then the local polynomial of `W` is
`1 - a T + q T ^ 2`, where `q` is the cardinality of the residue field and `a` is the trace of
Frobenius `WeierstrassCurve.localTrace`. -/
theorem localPolynomial_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) :
    W.localPolynomial R =
      1 - C (W.localTrace R) * X + C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  sorry

end WeierstrassCurve
