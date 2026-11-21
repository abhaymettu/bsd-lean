/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib

/-!
# Basic properties of the L-function of a Weierstrass curve over a number field

Mathlib defines the L-function `WeierstrassCurve.LFunction` of a Weierstrass curve over a number
field as the Euler product of the local Euler factors `WeierstrassCurve.localEulerFactor` at the
completions of the ring of integers. This file proves that every local Euler factor is a
multiplicative arithmetic function, and hence that so is the L-function; in particular its first
coefficient is `1`. Over `ℚ` it computes the coefficient of the L-function at a prime power
`p ^ k` as the `k`-th coefficient of the local power series at the place above `p`.
-/

namespace WeierstrassCurve

open ArithmeticFunction IsDedekindDomain NumberField

section LocalField

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

private lemma constantCoeff_localPowerSeries' :
    PowerSeries.constantCoeff (W.localPowerSeries R) = 1 := by
  rw [localPowerSeries, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]

/-- The local Euler factor of a Weierstrass curve is a multiplicative arithmetic function. If the
residue field is infinite, the junk value of `ArithmeticFunction.ofPowerSeries` makes it `1`. -/
theorem isMultiplicative_localEulerFactor : (W.localEulerFactor R).IsMultiplicative := by
  rcases finite_or_infinite (IsLocalRing.ResidueField R) with h | h
  · have := Fintype.ofFinite (IsLocalRing.ResidueField R)
    refine isMultiplicative_ofPowerSeries_of_isPrimePow _ ?_ _
      (W.constantCoeff_localPowerSeries' R)
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card _
  · rw [localEulerFactor, Nat.card_eq_zero_of_infinite]
    convert isMultiplicative_one
    simp [ofPowerSeries, W.constantCoeff_localPowerSeries' R]

end LocalField

section NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The L-function of a Weierstrass curve over a number field is a multiplicative arithmetic
function. -/
theorem isMultiplicative_LFunction : W.LFunction.IsMultiplicative :=
  isMultiplicative_eulerProduct _ fun _ ↦ isMultiplicative_localEulerFactor _ _

/-- The first coefficient of the L-function of a Weierstrass curve over a number field is `1`. -/
theorem LFunction_apply_one : W.LFunction 1 = 1 :=
  W.isMultiplicative_LFunction.map_one

end NumberField

section Rat

open Rat.HeightOneSpectrum

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The residue field of the completion of `ℚ` at `v` has cardinality the prime below `v`. -/
private lemma card_residueField_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = primesEquiv v := by
  rw [Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv
    (adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans PadicInt.residueField).toEquiv,
    Nat.card_zmod]

/-- Only finitely many places of `ℚ` have residue field of cardinality at most a given bound. -/
private instance northcott_card_residueField :
    Northcott fun v : HeightOneSpectrum (𝓞 ℚ) ↦
      Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) where
  finite_le b := by
    simp_rw [card_residueField_adicCompletionIntegers]
    exact ((Set.finite_Iic b).preimage Subtype.val_injective.injOn).preimage
      primesEquiv.injective.injOn

/-- The Dirichlet series `f(ℓ⁻ˢ)` vanishes at the nontrivial powers of a prime `p ≠ ℓ`. -/
private lemma ofPowerSeries_apply_pow_of_ne {R : Type*} [CommRing R] {ℓ p : ℕ} (hℓ : ℓ.Prime)
    (hp : p.Prime) (h : ℓ ≠ p) {f : PowerSeries R} (hf : f.constantCoeff = 1) (i : ℕ) :
    ofPowerSeries ℓ f (p ^ i) = if i = 0 then 1 else 0 := by
  rcases i with _ | i
  · rw [pow_zero, ofPowerSeries_apply_one, hf, ite_eq_left rfl]
  · rw [ofPowerSeries_apply hℓ.one_lt, Function.extend_apply', Pi.zero_apply,
      ite_eq_right i.succ_ne_zero]
    rintro ⟨j, hj⟩
    have : p ∣ ℓ ^ j := hj ▸ dvd_pow_self p i.succ_ne_zero
    exact h ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow this)).symm

/-- A finite product of Dirichlet series `fᵢ(qᵢ⁻ˢ)` with distinct prime bases, evaluated at a
power of one of the bases `q i₀`, only sees the factor at `i₀`. -/
private lemma prod_ofPowerSeries_apply_pow {ι R : Type*} [CommRing R] [DecidableEq ι]
    (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (f : ι → PowerSeries R)
    (hf : ∀ i, (f i).constantCoeff = 1) {i₀ : ι} (hi₀ : ∀ i, q i = q i₀ → i = i₀) (k : ℕ)
    (s : Finset ι) :
    (∏ i ∈ s, ofPowerSeries (q i) (f i)) (q i₀ ^ k) =
      if i₀ ∈ s then PowerSeries.coeff k (f i₀) else if k = 0 then 1 else 0 := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simp
    · rw [Finset.prod_empty, one_apply_ne (Nat.one_lt_pow k.succ_ne_zero (hq i₀).one_lt).ne']
      simp
  | insert w s hw ih =>
    rw [Finset.prod_insert hw, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b ↦ ofPowerSeries (q w) (f w) a * (∏ i ∈ s, ofPowerSeries (q i) (f i)) b),
      Nat.divisors_prime_pow (hq i₀), Finset.sum_map]
    have hdiv (x : ℕ) (hx : x ∈ Finset.range (k + 1)) :
        q i₀ ^ k / q i₀ ^ x = q i₀ ^ (k - x) :=
      Nat.pow_div (Finset.mem_range_succ_iff.mp hx) (hq i₀).pos
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.sum_congr rfl fun x hx ↦ by rw [hdiv x hx, ih]]
    by_cases hw₀ : w = i₀
    · subst hw₀
      rw [ite_eq_left (Finset.mem_insert_self w s), Finset.sum_eq_single k]
      · simp [hw, ofPowerSeries_apply_pow (hq w).one_lt]
      · intro x hx hxk
        simp [hw, show k - x ≠ 0 by have := Finset.mem_range_succ_iff.mp hx; omega]
      · simp
    · have hqw : q w ≠ q i₀ := fun h ↦ hw₀ (hi₀ w h)
      rw [Finset.sum_eq_single 0]
      · simp [hf w, Finset.mem_insert, Ne.symm hw₀]
      · intro x _ hx
        simp [ofPowerSeries_apply_pow_of_ne (hq w) (hq i₀) hqw (hf w), hx]
      · simp

/-- The coefficient of the L-function of a Weierstrass curve over `ℚ` at a prime power `p ^ k` is
the `k`-th coefficient of the local power series at the place `v` corresponding to `p`. -/
theorem LFunction_apply_primesEquiv_pow (W : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (k : ℕ) :
    W.LFunction ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ k) =
      PowerSeries.coeff k
        ((W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)) := by
  classical
  have hqv (w : HeightOneSpectrum (𝓞 ℚ)) :
      Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) = primesEquiv w :=
    card_residueField_adicCompletionIntegers w
  have hf (w : HeightOneSpectrum (𝓞 ℚ)) := (W.baseChange (w.adicCompletion ℚ))
    |>.constantCoeff_localPowerSeries' (w.adicCompletionIntegers ℚ)
  obtain ⟨s, hs, hvs⟩ := ((tendsTo_eulerProduct_ofPowerSeries
    (fun w : HeightOneSpectrum (𝓞 ℚ) ↦
      Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ))) _ hf
    ((primesEquiv v : ℕ) ^ k)).and
      (Filter.eventually_ge_atTop {v})).exists
  have key := prod_ofPowerSeries_apply_pow _ (fun w ↦ hqv w ▸ (primesEquiv w).2) _ hf
    (i₀ := v) (fun w h ↦ primesEquiv.injective (Subtype.ext (by rwa [hqv, hqv] at h))) k s
  rw [hqv v, ite_eq_left (hvs (Finset.mem_singleton_self v))] at key
  exact hs.symm.trans key

end Rat

end WeierstrassCurve
