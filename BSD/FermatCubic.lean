/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib

/-!
# The Mordell-Weil group of the Fermat cubic

The Fermat cubic `u³ + v³ = 1` has the Weierstrass model `E : y² = x³ - 432`, an elliptic curve
over `ℚ` of conductor 27. Using Fermat's Last Theorem for exponent 3 (`fermatLastTheoremThree`), we
determine all rational points of `E` and its group of rational points.

## Main results

* `FermatCubic.eq_or_eq_of_cube_add_cube_eq_one`: the rational solutions of `u³ + v³ = 1` are
  `(1, 0)` and `(0, 1)`.
* `FermatCubic.eq_of_sq_eq`: the affine rational points of `y² = x³ - 432` are `(12, 36)` and
  `(12, -36)`.
* `FermatCubic.natCard_point`: `E(ℚ)` has exactly three elements.
* `FermatCubic.nonempty_point_addEquiv_zmod`: `E(ℚ) ≃+ ZMod 3`.
* `FermatCubic.finrank_point`: `E(ℚ)` has rank `0`.
-/

namespace FermatCubic

open WeierstrassCurve

/-- The elliptic curve `y² = x³ - 432` over `ℚ`, a Weierstrass model of the Fermat cubic
`u³ + v³ = 1`. -/
def E : Affine ℚ := ⟨0, 0, 0, 0, -432⟩

theorem isElliptic : E.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  simp [E, Δ, b₂, b₄, b₆, b₈]

instance : E.IsElliptic := isElliptic

theorem equation_iff (x y : ℚ) : E.Equation x y ↔ y ^ 2 = x ^ 3 - 432 := by
  simp only [Affine.equation_iff, E]
  constructor <;> intro h <;> linear_combination h

/-- A rational number is determined by its cube. -/
private lemma eq_of_cube_eq {a b : ℚ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.strictMono_pow (by decide)).injective h

/-- The rational points of the Fermat cubic `u³ + v³ = 1` are `(1, 0)` and `(0, 1)`. -/
theorem eq_or_eq_of_cube_add_cube_eq_one {u v : ℚ} (h : u ^ 3 + v ^ 3 = 1) :
    u = 1 ∧ v = 0 ∨ u = 0 ∧ v = 1 := by
  have flt := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree
  by_cases hu : u = 0
  · subst hu
    exact .inr ⟨rfl, eq_of_cube_eq (by linear_combination h)⟩
  by_cases hv : v = 0
  · subst hv
    exact .inl ⟨eq_of_cube_eq (by linear_combination h), rfl⟩
  exact absurd (by rw [h, one_pow]) (flt u v 1 hu hv one_ne_zero)

/-- The affine rational points of `y² = x³ - 432` are `(12, 36)` and `(12, -36)`. -/
theorem eq_of_sq_eq {x y : ℚ} (h : y ^ 2 = x ^ 3 - 432) : x = 12 ∧ (y = 36 ∨ y = -36) := by
  have hx : x ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg y]
  have h6x : 6 * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have huv : ((36 + y) / (6 * x)) ^ 3 + ((36 - y) / (6 * x)) ^ 3 = 1 := by
    field_simp
    linear_combination 216 * h
  have hy : y = 36 ∨ y = -36 := by
    rcases eq_or_eq_of_cube_add_cube_eq_one huv with ⟨-, hv⟩ | ⟨hu, -⟩
    · rw [div_eq_zero_iff, or_iff_left h6x, sub_eq_zero] at hv
      exact .inl hv.symm
    · rw [div_eq_zero_iff, or_iff_left h6x, add_eq_zero_iff_eq_neg] at hu
      exact .inr (by linarith)
  refine ⟨eq_of_cube_eq ?_, hy⟩
  rcases hy with rfl | rfl <;> linear_combination -h

/-- The group of rational points of `y² = x³ - 432` has exactly three elements. -/
theorem natCard_point : Nat.card E.Point = 3 := by
  have h₁ : E.Equation 12 36 := (equation_iff 12 36).mpr (by norm_num)
  have h₂ : E.Equation 12 (-36) := (equation_iff 12 (-36)).mpr (by norm_num)
  rw [← Set.ncard_univ, Set.ncard_eq_three]
  refine ⟨0, Affine.Point.mk h₁, Affine.Point.mk h₂, nofun, nofun, ?_, ?_⟩
  · simp only [Affine.Point.mk, ne_eq, Affine.Point.some.injEq, true_and]
    norm_num
  refine Set.eq_of_subset_of_subset (fun P _ ↦ ?_) (Set.subset_univ _)
  rcases P with _ | ⟨x, y, hP⟩
  · exact .inl rfl
  obtain ⟨rfl, rfl | rfl⟩ := eq_of_sq_eq ((equation_iff x y).mp hP.1)
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- The group of rational points of `y² = x³ - 432` is cyclic of order three. -/
theorem nonempty_point_addEquiv_zmod : Nonempty (E.Point ≃+ ZMod 3) := by
  have := isAddCyclic_of_prime_card natCard_point
  exact ⟨addEquivOfAddCyclicCardEq (by rw [natCard_point, Nat.card_zmod])⟩

/-- The elliptic curve `y² = x³ - 432` has Mordell-Weil rank zero over `ℚ`. -/
theorem finrank_point : Module.finrank ℤ E.Point = 0 := by
  have : Finite E.Point := Nat.finite_of_card_ne_zero (by rw [natCard_point]; norm_num)
  refine Module.finrank_eq_zero_iff.mpr fun P ↦ ⟨3, by norm_num, ?_⟩
  rw [show (3 : ℤ) = (Nat.card E.Point : ℤ) by rw [natCard_point]; rfl, natCast_zsmul,
    card_nsmul_eq_zero']

/-! ### Further results -/

/-- The rational point `(12, 36)` of `y² = x³ - 432`, a generator of `E(ℚ)`. -/
def P₀ : E.Point :=
  Affine.Point.mk ((equation_iff 12 36).mpr (by norm_num))

/-- Every rational point of `y² = x³ - 432` is `0`, `P₀ = (12, 36)` or `-P₀ = (12, -36)`. -/
theorem point_eq (P : E.Point) : P = 0 ∨ P = P₀ ∨ P = -P₀ := by
  rcases P with _ | ⟨x, y, hP⟩
  · exact .inl rfl
  obtain ⟨rfl, rfl | rfl⟩ := eq_of_sq_eq ((equation_iff x y).mp hP.1)
  · exact .inr (.inl rfl)
  · refine .inr (.inr ?_)
    simp only [P₀, Affine.Point.mk, Affine.Point.neg_some, Affine.Point.some.injEq, true_and]
    norm_num [Affine.negY, E]

/-- Every rational point of `y² = x³ - 432` is `3`-torsion. -/
theorem three_nsmul (P : E.Point) : 3 • P = 0 :=
  natCard_point ▸ card_nsmul_eq_zero'

end FermatCubic
