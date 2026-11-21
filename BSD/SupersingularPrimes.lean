/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib
import BSD.LFunctionRatIntegral
import BSD.FermatCubic

/-!
# Vanishing coefficients of the L-functions of `y² = x³ + b` and `y² = x³ + a x`

For a prime `p ≡ 2 mod 3`, cubing is a bijection of `𝔽_p`, so the curve `y² = x³ + b` has exactly
`p + 1` points over `𝔽_p`. With `WeierstrassCurve.LFunction_baseChange_apply_of_not_dvd` this gives
`a_p = 0` for the L-function of `y² = x³ + b` over `ℚ` at every prime `p ≡ 2 mod 3` with `p ≠ 2`
and `p ∤ b` (the supersingular primes of a curve with `j = 0`). The same holds for
`y² = x³ + a x` at primes `p ≡ 3 mod 4` with `p ∤ a` (`j = 1728`).

For the Fermat cubic `E : y² = x³ - 432` this computes infinitely many coefficients of Mathlib's
L-function, and two coefficients at primes `p ≡ 1 mod 3` are computed by counting points.

## Main results

* `WeierstrassCurve.Affine.natCard_point_of_mod_three_eq_two`: `|E(𝔽_p)| = p + 1` for
  `E : y² = x³ + b` and `p ≡ 2 mod 3`.
* `WeierstrassCurve.LFunction_apply_of_mod_three_eq_two`: `a_p = 0` for `y² = x³ + b`.
* `WeierstrassCurve.LFunction_apply_sq_of_mod_three_eq_two`: `a_{p²} = -p` for `y² = x³ + b`.
* `WeierstrassCurve.Affine.natCard_point_of_mod_four_eq_three`: `|E(𝔽_p)| = p + 1` for
  `E : y² = x³ + a x` and `p ≡ 3 mod 4`.
* `WeierstrassCurve.LFunction_apply_of_mod_four_eq_three`: `a_p = 0` for `y² = x³ + a x`.
* `FermatCubic.LFunction_apply_of_mod_three_eq_two`: `a_p = 0` for the Fermat cubic.
* `FermatCubic.infinite_setOf_prime_and_LFunction_eq_zero`: infinitely many `a_p` vanish.
* `FermatCubic.LFunction_apply_seven`, `FermatCubic.LFunction_apply_thirteen`: `a_7 = -1` and
  `a_13 = 5`.
-/

namespace WeierstrassCurve

private lemma pow_three_injective_of_mod_three_eq_two (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Injective fun x : ZMod p ↦ x ^ 3 := by
  intro x y (h : x ^ 3 = y ^ 3)
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using h
  have hz : (x / y) ^ 3 = 1 := by rw [div_pow, h, div_self (pow_ne_zero 3 hy)]
  have hz0 : x / y ≠ 0 := by
    rintro h0
    rw [h0] at hz
    simp at hz
  have hk : p - 1 = 3 * (p / 3) + 1 := by
    have := Nat.div_add_mod p 3
    omega
  have := ZMod.pow_card_sub_one_eq_one hz0
  rw [hk, pow_succ, pow_mul, hz, one_pow, one_mul] at this
  rwa [div_eq_one_iff_eq hy] at this

private lemma pow_three_bijective_of_mod_three_eq_two (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Bijective fun x : ZMod p ↦ x ^ 3 :=
  Finite.injective_iff_bijective.mp (pow_three_injective_of_mod_three_eq_two p hp)

/-- If `p ≡ 2 mod 3`, the curve `y² = x³ + b` over `𝔽_p` with nonzero discriminant has exactly
`p + 1` points: cubing is a bijection of `𝔽_p`, so each `y` determines one `x`. -/
theorem Affine.natCard_point_of_mod_three_eq_two (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (b : ZMod p) (hΔ : (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0) :
    Nat.card (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve (ZMod p)).toAffine.Point = p + 1 := by
  set W : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, 0, b⟩
  have hW (x y : ZMod p) : W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + b := by
    rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
    simp [W]
  have hbij : Function.Bijective
      fun xy : {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} ↦ xy.1.2 := by
    obtain ⟨hinj, hsurj⟩ := pow_three_bijective_of_mod_three_eq_two p hp
    refine ⟨?_, fun y ↦ ?_⟩
    · rintro ⟨⟨x, y⟩, h⟩ ⟨⟨x', y'⟩, h'⟩ (rfl : y = y')
      rw [hW] at h h'
      have : x = x' := hinj (show x ^ 3 = x' ^ 3 by linear_combination h' - h)
      subst this
      rfl
    · obtain ⟨x, hx⟩ := hsurj (y ^ 2 - b)
      exact ⟨⟨⟨x, y⟩, (hW x y).mpr (by linear_combination -hx)⟩, rfl⟩
  rw [Nat.card_congr (Affine.nonsingularPointEquiv _)]
  change Nat.card (Option _) = _
  rw [Finite.card_option, Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_zmod]

private lemma not_dvd_four_hundred_thirty_two (p : ℕ) [hpp : Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 ^ 4 * 3 ^ 3 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp.out
  intro h
  rcases hpz.dvd_or_dvd h with h | h
  · have := Int.natCast_dvd_natCast.mp (hpz.dvd_of_dvd_pow (n := 4) (by exact_mod_cast h))
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp.out Nat.prime_two).mp this)
  · have := Int.natCast_dvd_natCast.mp (hpz.dvd_of_dvd_pow (n := 3) (by exact_mod_cast h))
    have := (Nat.prime_dvd_prime_iff_eq hpp.out Nat.prime_three).mp this
    omega

private lemma not_dvd_Δ_of_mod_three_eq_two (b : ℤ) (p : ℕ) [hpp : Fact p.Prime]
    (hp : p % 3 = 2) (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ∣ (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve ℤ).Δ := by
  have hΔ : (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve ℤ).Δ = -(2 ^ 4 * 3 ^ 3 * b ^ 2) := by
    simp only [Δ, b₂, b₄, b₆, b₈]
    ring
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp.out
  rw [hΔ, dvd_neg]
  intro h
  rcases hpz.dvd_or_dvd h with h | h
  · exact not_dvd_four_hundred_thirty_two p hp hp2 h
  · exact hb (hpz.dvd_of_dvd_pow h)

/-- The L-function of `y² = x³ + b` over `ℚ` has `a_p = 0` at every prime `p ≡ 2 mod 3` with
`p ≠ 2` and `p ∤ b`. -/
theorem LFunction_apply_of_mod_three_eq_two (b : ℤ) (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b) :
    ((⟨0, 0, 0, 0, b⟩ : WeierstrassCurve ℤ).baseChange ℚ).LFunction p = 0 := by
  have h := not_dvd_Δ_of_mod_three_eq_two b p hp hp2 hb
  have hW : (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve ℤ).baseChange (ZMod p) =
      ⟨0, 0, 0, 0, (b : ZMod p)⟩ := by
    ext <;> simp [baseChange]
  rw [LFunction_baseChange_apply_of_not_dvd _ p h, hW,
    Affine.natCard_point_of_mod_three_eq_two p hp]
  · push_cast
    ring
  · rw [← hW, baseChange, map_Δ, ne_eq, algebraMap_int_eq, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h

/-- The L-function of `y² = x³ + b` over `ℚ` has `a_{p²} = -p` at every prime `p ≡ 2 mod 3` with
`p ≠ 2` and `p ∤ b`. -/
theorem LFunction_apply_sq_of_mod_three_eq_two (b : ℤ) (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b) :
    ((⟨0, 0, 0, 0, b⟩ : WeierstrassCurve ℤ).baseChange ℚ).LFunction (p ^ 2) = -p := by
  have h := LFunction_baseChange_apply_pow_add_two_of_not_dvd _ p
    (not_dvd_Δ_of_mod_three_eq_two b p hp hp2 hb) 0
  rw [zero_add, pow_one, pow_zero, LFunction_apply_of_mod_three_eq_two b p hp hp2 hb,
    LFunction_apply_one] at h
  rw [h]
  ring

/-- If `-1` is not a square in a finite field and `f` is odd, then the quadratic characters of
the values of `f` sum to zero. -/
private lemma sum_quadraticChar_eq_zero_of_odd {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h1 : ¬ IsSquare (-1 : F)) (f : F → F) (hf : ∀ x, f (-x) = -f x) :
    ∑ x, quadraticChar F (f x) = 0 := by
  have hneg : quadraticChar F (-1) = -1 := (quadraticChar_neg_one_iff_not_isSquare).mpr h1
  have h : ∑ x, quadraticChar F (f x) = -∑ x, quadraticChar F (f x) := by
    calc ∑ x, quadraticChar F (f x) = ∑ x, quadraticChar F (f (-x)) :=
          (Equiv.sum_comp (Equiv.neg F) fun x ↦ quadraticChar F (f x)).symm
      _ = -∑ x, quadraticChar F (f x) := by
          simp only [hf, neg_eq_neg_one_mul (f _), map_mul, hneg, ← Finset.sum_neg_distrib]
          simp
  linarith

/-- If `p ≡ 3 mod 4`, the curve `y² = x³ + a x` over `𝔽_p` with nonzero discriminant has exactly
`p + 1` points: `-1` is not a square, so `x` and `-x` together contribute two points. -/
theorem Affine.natCard_point_of_mod_four_eq_three (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (a : ZMod p) (hΔ : (⟨0, 0, 0, a, 0⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0) :
    Nat.card (⟨0, 0, 0, a, 0⟩ : WeierstrassCurve (ZMod p)).toAffine.Point = p + 1 := by
  set W : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, a, 0⟩
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have h1 : ¬ IsSquare (-1 : ZMod p) := by
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
    omega
  have hW (x y : ZMod p) : W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + a * x := by
    rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
    simp [W]
  rw [Nat.card_congr (Affine.nonsingularPointEquiv _)]
  change Nat.card (Option _) = _
  rw [Finite.card_option]
  have e1 := Nat.card_congr (Equiv.subtypeEquivRight fun xy : ZMod p × ZMod p ↦ hW xy.1 xy.2)
  have e2 := Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun x y : ZMod p ↦ y ^ 2 = x ^ 3 + a * x)
  rw [e1, e2, Nat.card_sigma]
  have key : ((∑ x : ZMod p, Nat.card {y : ZMod p // y ^ 2 = x ^ 3 + a * x} : ℕ) : ℤ) = p := by
    push_cast
    simp_rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Set.toFinset_ofPred,
      quadraticChar_card_sqrts hF]
    rw [Finset.sum_add_distrib, sum_quadraticChar_eq_zero_of_odd h1 _ fun x ↦ by ring]
    simp
  omega

/-- The L-function of `y² = x³ + a x` over `ℚ` has `a_p = 0` at every prime `p ≡ 3 mod 4` with
`p ∤ a`. -/
theorem LFunction_apply_of_mod_four_eq_three (a : ℤ) (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (ha : ¬ (p : ℤ) ∣ a) :
    ((⟨0, 0, 0, a, 0⟩ : WeierstrassCurve ℤ).baseChange ℚ).LFunction p = 0 := by
  have hpp : p.Prime := Fact.out
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have h : ¬ (p : ℤ) ∣ (⟨0, 0, 0, a, 0⟩ : WeierstrassCurve ℤ).Δ := by
    have hΔ : (⟨0, 0, 0, a, 0⟩ : WeierstrassCurve ℤ).Δ = -(2 ^ 6 * a ^ 3) := by
      simp only [Δ, b₂, b₄, b₆, b₈]
      ring
    rw [hΔ, dvd_neg]
    intro h
    rcases hpz.dvd_or_dvd h with h | h
    · have := Int.natCast_dvd_natCast.mp (hpz.dvd_of_dvd_pow (n := 6) (by exact_mod_cast h))
      have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this
      omega
    · exact ha (hpz.dvd_of_dvd_pow h)
  have hW : (⟨0, 0, 0, a, 0⟩ : WeierstrassCurve ℤ).baseChange (ZMod p) =
      ⟨0, 0, 0, (a : ZMod p), 0⟩ := by
    ext <;> simp [baseChange]
  rw [LFunction_baseChange_apply_of_not_dvd _ p h, hW,
    Affine.natCard_point_of_mod_four_eq_three p hp]
  · push_cast
    ring
  · rw [← hW, baseChange, map_Δ, ne_eq, algebraMap_int_eq, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h

end WeierstrassCurve

namespace FermatCubic

open WeierstrassCurve

private lemma E_eq : E = (⟨0, 0, 0, 0, -432⟩ : WeierstrassCurve ℤ).baseChange ℚ := by
  ext <;> simp [E, baseChange]

private lemma natCard_point_eq (p : ℕ) [Fact p.Prime] [DecidableEq (ZMod p)]
    (hΔ : (⟨0, 0, 0, 0, -432⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0) :
    Nat.card ((⟨0, 0, 0, 0, -432⟩ : WeierstrassCurve ℤ).baseChange (ZMod p)).toAffine.Point =
      (Finset.univ.filter fun xy : ZMod p × ZMod p ↦ xy.2 ^ 2 = xy.1 ^ 3 - 432).card + 1 := by
  have hW : (⟨0, 0, 0, 0, -432⟩ : WeierstrassCurve ℤ).baseChange (ZMod p) =
      ⟨0, 0, 0, 0, -432⟩ := by
    ext <;> simp [baseChange]
  rw [hW, Nat.card_congr (Affine.nonsingularPointEquiv _)]
  change Nat.card (Option _) = _
  rw [Finite.card_option, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun xy ↦ ?_)
  rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
  ring_nf

/-- The L-function of the Fermat cubic `y² = x³ - 432` has `a_p = 0` at every prime
`p ≡ 2 mod 3` with `p ≠ 2`. -/
theorem LFunction_apply_of_mod_three_eq_two (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) : E.LFunction p = 0 := by
  rw [E_eq]
  refine WeierstrassCurve.LFunction_apply_of_mod_three_eq_two _ p hp hp2 fun h ↦ ?_
  rw [dvd_neg] at h
  exact not_dvd_four_hundred_thirty_two p hp hp2 h

/-- Infinitely many prime coefficients of the L-function of the Fermat cubic vanish. -/
theorem infinite_setOf_prime_and_LFunction_eq_zero :
    {p : ℕ | p.Prime ∧ E.LFunction p = 0}.Infinite := by
  have hu : IsUnit (2 : ZMod 3) := by decide
  refine ((Nat.infinite_setOfPred_prime_and_eq_mod hu).sdiff (Set.finite_singleton 2)).mono ?_
  rintro p ⟨⟨hp, hp3⟩, hp2⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp3' : p % 3 = 2 := by
    rw [← ZMod.val_natCast, hp3]
    rfl
  exact ⟨hp, LFunction_apply_of_mod_three_eq_two p hp3' hp2⟩

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The coefficient `a_7` of the L-function of the Fermat cubic is `-1`. -/
theorem LFunction_apply_seven : E.LFunction 7 = -1 := by
  rw [E_eq, LFunction_baseChange_apply_of_not_dvd _ 7 (by decide), natCard_point_eq 7 (by decide)]
  decide

/-- The coefficient `a_13` of the L-function of the Fermat cubic is `5`. -/
theorem LFunction_apply_thirteen : E.LFunction 13 = 5 := by
  rw [E_eq, LFunction_baseChange_apply_of_not_dvd _ 13 (by decide),
    natCard_point_eq 13 (by decide)]
  decide

end FermatCubic
