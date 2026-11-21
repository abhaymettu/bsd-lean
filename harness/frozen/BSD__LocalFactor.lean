/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib

/-!
# Basic properties of the local factors of the L-function of a Weierstrass curve

Mathlib defines the local polynomial `WeierstrassCurve.localPolynomial`, the local power series
`WeierstrassCurve.localPowerSeries` and the local Euler factor `WeierstrassCurve.localEulerFactor` of a
Weierstrass curve over the fraction field of a discrete valuation ring. This file provides their first
API: the value of the local polynomial in each reduction type, its constant coefficient and degree, the
fact that the local power series is its inverse, the resulting recursion for the coefficients (the Hecke
recursion `a_{q^(n+2)} = a_q * a_{q^(n+1)} - q * a_{q^n}` in the case of good reduction), and the values
of the local Euler factor at powers of the residue cardinality.
-/

namespace WeierstrassCurve

open Polynomial

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

/-- The trace of Frobenius `q + 1 - |W̃(κ)|` of the reduction of a minimal model of `W`, where `κ` is
the residue field and `q` is its cardinality. -/
noncomputable def localTrace : ℤ :=
  Nat.card (IsLocalRing.ResidueField R) + 1 - Nat.card ((W.minimal R).reduction R).toAffine.Point

theorem localPolynomial_of_hasGoodReduction (h : (W.minimal R).HasGoodReduction R) :
    W.localPolynomial R =
      1 - C (W.localTrace R) * X + C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  sorry

theorem localPolynomial_of_hasSplitMultiplicativeReduction
    (h : (W.minimal R).HasSplitMultiplicativeReduction R) : W.localPolynomial R = 1 - X := by
  sorry

theorem localPolynomial_of_hasMultiplicativeReduction (h : (W.minimal R).HasMultiplicativeReduction R)
    (h' : ¬ (W.minimal R).HasSplitMultiplicativeReduction R) : W.localPolynomial R = 1 + X := by
  sorry

theorem localPolynomial_of_hasAdditiveReduction (h : (W.minimal R).HasAdditiveReduction R) :
    W.localPolynomial R = 1 := by
  sorry

theorem coeff_zero_localPolynomial : (W.localPolynomial R).coeff 0 = 1 := by
  sorry

theorem natDegree_localPolynomial_le : (W.localPolynomial R).natDegree ≤ 2 := by
  sorry

theorem localPolynomial_mul_localPowerSeries :
    (W.localPolynomial R : PowerSeries ℤ) * W.localPowerSeries R = 1 := by
  sorry

theorem constantCoeff_localPowerSeries : PowerSeries.constantCoeff (W.localPowerSeries R) = 1 := by
  sorry

theorem coeff_one_localPowerSeries :
    PowerSeries.coeff 1 (W.localPowerSeries R) = -(W.localPolynomial R).coeff 1 := by
  sorry

/-- The recursion satisfied by the coefficients of the local power series. In the case of good reduction
this is the Hecke recursion `a_{q^(n+2)} = a_q * a_{q^(n+1)} - q * a_{q^n}`. -/
theorem coeff_add_two_localPowerSeries (n : ℕ) :
    PowerSeries.coeff (n + 2) (W.localPowerSeries R) =
      -(W.localPolynomial R).coeff 1 * PowerSeries.coeff (n + 1) (W.localPowerSeries R) -
        (W.localPolynomial R).coeff 2 * PowerSeries.coeff n (W.localPowerSeries R) := by
  sorry

theorem localEulerFactor_apply_one : W.localEulerFactor R 1 = 1 := by
  sorry

theorem localEulerFactor_apply_pow (hq : 1 < Nat.card (IsLocalRing.ResidueField R)) (k : ℕ) :
    W.localEulerFactor R (Nat.card (IsLocalRing.ResidueField R) ^ k) =
      PowerSeries.coeff k (W.localPowerSeries R) := by
  sorry

/-- In the case of good reduction, the coefficient of the local Euler factor at the residue
cardinality `q` is the trace of Frobenius. -/
theorem localEulerFactor_apply_card_of_hasGoodReduction (h : (W.minimal R).HasGoodReduction R)
    (hq : 1 < Nat.card (IsLocalRing.ResidueField R)) :
    W.localEulerFactor R (Nat.card (IsLocalRing.ResidueField R)) = W.localTrace R := by
  sorry

end WeierstrassCurve
