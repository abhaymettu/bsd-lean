/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib
import BSD.LocalFactor
import BSD.LFunctionBasic

/-!
# The Euler product of the L-function of an elliptic curve over `ℚ`

Let `W` be a Weierstrass curve over `ℚ`, let `v` be a finite place of `ℚ` and let `p` be the prime
below `v`. Write `K_v` for the completion of `ℚ` at `v`, `O_v` for its ring of integers and
`W_v` for the base change of `W` to `K_v`. This file computes the coefficients of Mathlib's
L-function `WeierstrassCurve.LFunction` at the powers of `p` in terms of the reduction type of a
minimal model of `W_v`, the classical description of the Euler product
`L(W, s) = ∏_p L_p(W, p⁻ˢ)⁻¹`:

* if `W_v` has good reduction, `a_p = p + 1 - |W̃(𝔽_p)|` and
  `a_{p^(n+2)} = a_p * a_{p^(n+1)} - p * a_{p^n}`;
* if `W_v` has split multiplicative reduction, `a_{p^k} = 1`;
* if `W_v` has non-split multiplicative reduction, `a_{p^k} = (-1) ^ k`;
* if `W_v` has additive reduction, `a_{p^k} = 0` for `k ≥ 1`.

## Main results

* `Rat.HeightOneSpectrum.card_residueField_adicCompletionIntegers`: the residue field of `O_v` has
  `p` elements.
* `WeierstrassCurve.LFunction_apply_primesEquiv_of_hasGoodReduction`: `a_p` is the local trace.
* `WeierstrassCurve.LFunction_apply_primesEquiv_eq_sub_natCard`: `a_p = p + 1 - |W̃(𝔽_p)|`.
* `WeierstrassCurve.LFunction_apply_primesEquiv_pow_add_two`: the Hecke recursion.
* `WeierstrassCurve.LFunction_apply_primesEquiv_pow_of_hasSplitMultiplicativeReduction`,
  `WeierstrassCurve.LFunction_apply_primesEquiv_pow_of_hasNonsplitMultiplicativeReduction`,
  `WeierstrassCurve.LFunction_apply_primesEquiv_pow_of_hasAdditiveReduction`: the bad primes.
-/

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

namespace Rat.HeightOneSpectrum

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The residue field of the ring of integers of the completion of `ℚ` at a finite place `v` has
cardinality the prime below `v`. -/
theorem card_residueField_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = primesEquiv v := by
  rw [Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv
    (adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans PadicInt.residueField).toEquiv,
    Nat.card_zmod]

end Rat.HeightOneSpectrum

namespace WeierstrassCurve

open Polynomial in
private lemma coeff_one_sub_C_mul_X (c : ℤ) :
    (1 - C c * X : ℤ[X]).coeff 1 = -c ∧ (1 - C c * X : ℤ[X]).coeff 2 = 0 := by
  rw [coeff_sub, coeff_sub, coeff_C_mul_X, coeff_C_mul_X, coeff_one, coeff_one]
  constructor <;> simp

open Polynomial in
/-- If the local polynomial of `W` is `1 - c X`, the local power series is `∑ cᵏ Xᵏ`. -/
private lemma coeff_localPowerSeries_of_localPolynomial_eq (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) {c : ℤ} (h : W.localPolynomial R = 1 - C c * X) (k : ℕ) :
    PowerSeries.coeff k (W.localPowerSeries R) = c ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_localPowerSeries, pow_zero]
    · rw [coeff_one_localPowerSeries, h, (coeff_one_sub_C_mul_X c).1, neg_neg, pow_one]
    · rw [coeff_add_two_localPowerSeries, h, ih (k + 1) (by omega), ih k (by omega),
        (coeff_one_sub_C_mul_X c).1, (coeff_one_sub_C_mul_X c).2]
      ring

open Polynomial in
private lemma coeff_one_and_two (a q : ℤ) :
    (1 - C a * X + C q * X ^ 2 : ℤ[X]).coeff 1 = -a ∧
      (1 - C a * X + C q * X ^ 2 : ℤ[X]).coeff 2 = q := by
  rw [coeff_add, coeff_add, coeff_sub, coeff_sub, coeff_C_mul_X, coeff_C_mul_X, coeff_one,
    coeff_one, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  constructor <;> simp

variable (W : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))

/-- If `W` has good reduction at the place `v` above `p`, the coefficient `a_p` of the L-function
of `W` is the trace of Frobenius `p + 1 - |W̃(𝔽_p)|` of the reduction of a minimal model. -/
theorem LFunction_apply_primesEquiv_of_hasGoodReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    W.LFunction (primesEquiv v : ℕ) =
      (W.baseChange (v.adicCompletion ℚ)).localTrace (v.adicCompletionIntegers ℚ) := by
  rw [← pow_one (primesEquiv v : ℕ), LFunction_apply_primesEquiv_pow, coeff_one_localPowerSeries,
    localPolynomial_of_hasGoodReduction _ _ h, (coeff_one_and_two _ _).1, neg_neg]

/-- If `W` has good reduction at the place `v` above `p`, then `a_p = p + 1 - |W̃(𝔽_p)|`, where
`W̃` is the reduction of a minimal model of `W` over the completion at `v`. -/
theorem LFunction_apply_primesEquiv_eq_sub_natCard
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    W.LFunction (primesEquiv v : ℕ) = ((primesEquiv v : ℕ) : ℤ) + 1 -
      Nat.card (((W.baseChange (v.adicCompletion ℚ)).minimal
        (v.adicCompletionIntegers ℚ)).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point := by
  rw [LFunction_apply_primesEquiv_of_hasGoodReduction W v h, localTrace,
    card_residueField_adicCompletionIntegers]

/-- The Hecke recursion: if `W` has good reduction at the place `v` above `p`, then
`a_{p^(n+2)} = a_p * a_{p^(n+1)} - p * a_{p^n}`. -/
theorem LFunction_apply_primesEquiv_pow_add_two
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) (n : ℕ) :
    W.LFunction ((primesEquiv v : ℕ) ^ (n + 2)) =
      W.LFunction (primesEquiv v : ℕ) * W.LFunction ((primesEquiv v : ℕ) ^ (n + 1)) -
        (primesEquiv v : ℕ) * W.LFunction ((primesEquiv v : ℕ) ^ n) := by
  rw [LFunction_apply_primesEquiv_of_hasGoodReduction W v h]
  simp only [LFunction_apply_primesEquiv_pow]
  rw [coeff_add_two_localPowerSeries, localPolynomial_of_hasGoodReduction _ _ h,
    (coeff_one_and_two _ _).1, (coeff_one_and_two _ _).2, card_residueField_adicCompletionIntegers,
    neg_neg]

/-- If `W` has split multiplicative reduction at the place `v` above `p`, then `a_{p^k} = 1`. -/
theorem LFunction_apply_primesEquiv_pow_of_hasSplitMultiplicativeReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        (v.adicCompletionIntegers ℚ))
    (k : ℕ) : W.LFunction ((primesEquiv v : ℕ) ^ k) = 1 := by
  rw [LFunction_apply_primesEquiv_pow, coeff_localPowerSeries_of_localPolynomial_eq _ _
    (c := 1) (by rw [localPolynomial_of_hasSplitMultiplicativeReduction _ _ h, map_one, one_mul]),
    one_pow]

/-- If `W` has non-split multiplicative reduction at the place `v` above `p`, then
`a_{p^k} = (-1) ^ k`. -/
theorem LFunction_apply_primesEquiv_pow_of_hasNonsplitMultiplicativeReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasMultiplicativeReduction (v.adicCompletionIntegers ℚ))
    (h' : ¬ ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        (v.adicCompletionIntegers ℚ))
    (k : ℕ) : W.LFunction ((primesEquiv v : ℕ) ^ k) = (-1) ^ k := by
  rw [LFunction_apply_primesEquiv_pow, coeff_localPowerSeries_of_localPolynomial_eq _ _
    (c := -1) (by rw [localPolynomial_of_hasMultiplicativeReduction _ _ h h', map_neg, map_one,
      neg_one_mul, sub_neg_eq_add])]

/-- If `W` has additive reduction at the place `v` above `p`, then `a_{p^k} = 0` for `k ≥ 1`. -/
theorem LFunction_apply_primesEquiv_pow_of_hasAdditiveReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasAdditiveReduction (v.adicCompletionIntegers ℚ))
    {k : ℕ} (hk : k ≠ 0) : W.LFunction ((primesEquiv v : ℕ) ^ k) = 0 := by
  rw [LFunction_apply_primesEquiv_pow, coeff_localPowerSeries_of_localPolynomial_eq _ _
    (c := 0) (by rw [localPolynomial_of_hasAdditiveReduction _ _ h, map_zero, zero_mul, sub_zero]),
    zero_pow hk]

end WeierstrassCurve
