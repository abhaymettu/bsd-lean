/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib

/-!
# Basic properties of the local factors of the L-function of a Weierstrass curve

Mathlib defines the local polynomial `WeierstrassCurve.localPolynomial`, the local power series
`WeierstrassCurve.localPowerSeries` and the local Euler factor `WeierstrassCurve.localEulerFactor`
of a Weierstrass curve over the fraction field of a discrete valuation ring. This file provides
their first API: the value of the local polynomial in each reduction type, its constant coefficient
and degree, the fact that the local power series is its inverse, the resulting recursion for the
coefficients (the Hecke recursion `a_{q^(n+2)} = a_q * a_{q^(n+1)} - q * a_{q^n}` in the case of
good reduction), and the values of the local Euler factor at powers of the residue cardinality.
-/

namespace WeierstrassCurve

open Polynomial

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

/-- The trace of Frobenius `q + 1 - |W̃(κ)|` of the reduction of a minimal model of `W`, where `κ`
is the residue field and `q` is its cardinality. -/
noncomputable def localTrace : ℤ :=
  Nat.card (IsLocalRing.ResidueField R) + 1 - Nat.card ((W.minimal R).reduction R).toAffine.Point

theorem localPolynomial_of_hasGoodReduction (h : (W.minimal R).HasGoodReduction R) :
    W.localPolynomial R =
      1 - C (W.localTrace R) * X + C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  simp only [localPolynomial, h, ↓reduceIte, localTrace]

theorem localPolynomial_of_hasSplitMultiplicativeReduction
    (h : (W.minimal R).HasSplitMultiplicativeReduction R) : W.localPolynomial R = 1 - X := by
  simp only [localPolynomial, h.not_hasGoodReduction, h, ↓reduceIte]

theorem localPolynomial_of_hasMultiplicativeReduction
    (h : (W.minimal R).HasMultiplicativeReduction R)
    (h' : ¬ (W.minimal R).HasSplitMultiplicativeReduction R) : W.localPolynomial R = 1 + X := by
  simp only [localPolynomial, h.not_hasGoodReduction, h', h, ↓reduceIte]

theorem localPolynomial_of_hasAdditiveReduction (h : (W.minimal R).HasAdditiveReduction R) :
    W.localPolynomial R = 1 := by
  have h' : ¬ (W.minimal R).HasSplitMultiplicativeReduction R :=
    fun h'' ↦ h.not_hasMultiplicativeReduction (R := R) h''.toHasMultiplicativeReduction
  simp only [localPolynomial, h.not_hasGoodReduction (R := R), h',
    h.not_hasMultiplicativeReduction (R := R), ↓reduceIte]

theorem coeff_zero_localPolynomial : (W.localPolynomial R).coeff 0 = 1 := by
  rw [localPolynomial]
  split_ifs <;> simp

theorem natDegree_localPolynomial_le : (W.localPolynomial R).natDegree ≤ 2 := by
  rw [localPolynomial]
  split_ifs <;> compute_degree!

theorem localPolynomial_mul_localPowerSeries :
    (W.localPolynomial R : PowerSeries ℤ) * W.localPowerSeries R = 1 := by
  rw [localPowerSeries, PowerSeries.mul_invOfUnit _ _ <| by
    rw [Polynomial.constantCoeff_coe, coeff_zero_localPolynomial, Units.val_one]]

/-- The local polynomial as a power series, written out in terms of its first three coefficients. -/
private lemma coe_localPolynomial :
    (W.localPolynomial R : PowerSeries ℤ) =
      1 + PowerSeries.C ((W.localPolynomial R).coeff 1) * PowerSeries.X ^ 1 +
        PowerSeries.C ((W.localPolynomial R).coeff 2) * PowerSeries.X ^ 2 := by
  ext k
  rw [map_add, map_add, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul_X_pow,
    PowerSeries.coeff_one, Polynomial.coeff_coe]
  rcases k with _ | _ | _ | k
  · simp [coeff_zero_localPolynomial]
  · simp
  · simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((natDegree_localPolynomial_le R W).trans_lt (by omega))]
    simp

/-- The coefficient of `X ^ n` in `localPolynomial * localPowerSeries`, expanded. -/
private lemma coeff_localPolynomial_mul_localPowerSeries (n : ℕ) :
    PowerSeries.coeff n ((W.localPolynomial R : PowerSeries ℤ) * W.localPowerSeries R) =
      PowerSeries.coeff n (W.localPowerSeries R) +
        (W.localPolynomial R).coeff 1 *
          (if 1 ≤ n then PowerSeries.coeff (n - 1) (W.localPowerSeries R) else 0) +
        (W.localPolynomial R).coeff 2 *
          (if 2 ≤ n then PowerSeries.coeff (n - 2) (W.localPowerSeries R) else 0) := by
  rw [coe_localPolynomial, add_mul, add_mul, one_mul, mul_assoc, mul_assoc, map_add, map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul']

theorem constantCoeff_localPowerSeries : PowerSeries.constantCoeff (W.localPowerSeries R) = 1 := by
  rw [localPowerSeries, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]

theorem coeff_one_localPowerSeries :
    PowerSeries.coeff 1 (W.localPowerSeries R) = -(W.localPolynomial R).coeff 1 := by
  have h := W.coeff_localPolynomial_mul_localPowerSeries R 1
  rw [localPolynomial_mul_localPowerSeries, PowerSeries.coeff_one, ite_eq_right one_ne_zero,
    ite_eq_left le_rfl, ite_eq_right (by omega), Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_localPowerSeries] at h
  linear_combination -h

/-- The recursion satisfied by the coefficients of the local power series. In the case of good
reduction this is the Hecke recursion `a_{q^(n+2)} = a_q * a_{q^(n+1)} - q * a_{q^n}`. -/
theorem coeff_add_two_localPowerSeries (n : ℕ) :
    PowerSeries.coeff (n + 2) (W.localPowerSeries R) =
      -(W.localPolynomial R).coeff 1 * PowerSeries.coeff (n + 1) (W.localPowerSeries R) -
        (W.localPolynomial R).coeff 2 * PowerSeries.coeff n (W.localPowerSeries R) := by
  have h := W.coeff_localPolynomial_mul_localPowerSeries R (n + 2)
  rw [localPolynomial_mul_localPowerSeries, PowerSeries.coeff_one, ite_eq_right (by omega),
    ite_eq_left (by omega), ite_eq_left (by omega), Nat.add_sub_cancel,
    show n + 2 - 1 = n + 1 by omega] at h
  linear_combination -h

theorem localEulerFactor_apply_one : W.localEulerFactor R 1 = 1 := by
  rw [localEulerFactor, ArithmeticFunction.ofPowerSeries_apply_one, constantCoeff_localPowerSeries]

theorem localEulerFactor_apply_pow (hq : 1 < Nat.card (IsLocalRing.ResidueField R)) (k : ℕ) :
    W.localEulerFactor R (Nat.card (IsLocalRing.ResidueField R) ^ k) =
      PowerSeries.coeff k (W.localPowerSeries R) :=
  ArithmeticFunction.ofPowerSeries_apply_pow hq _ k

/-- In the case of good reduction, the coefficient of the local Euler factor at the residue
cardinality `q` is the trace of Frobenius. -/
theorem localEulerFactor_apply_card_of_hasGoodReduction (h : (W.minimal R).HasGoodReduction R)
    (hq : 1 < Nat.card (IsLocalRing.ResidueField R)) :
    W.localEulerFactor R (Nat.card (IsLocalRing.ResidueField R)) = W.localTrace R := by
  rw [← pow_one (Nat.card (IsLocalRing.ResidueField R)), localEulerFactor_apply_pow R W hq,
    coeff_one_localPowerSeries, localPolynomial_of_hasGoodReduction R W h]
  simp only [coeff_add, coeff_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X_one]
  norm_num

end WeierstrassCurve
