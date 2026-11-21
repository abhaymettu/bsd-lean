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

/-- The coefficients of `W` in terms of those of `C • W`, cleared of `u⁻¹`. -/
private lemma u_pow_mul_variableChange_a :
    (C.u : S) * (C • W).a₁ = W.a₁ + 2 * C.s ∧
      (C.u : S) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 ∧
      (C.u : S) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t ∧
      (C.u : S) ^ 4 * (C • W).a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ +
        3 * C.r ^ 2 - 2 * C.s * C.t ∧
      (C.u : S) ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ -
        C.t ^ 2 - C.r * C.t * W.a₁ := by
  have h (n : ℕ) (a : S) : (C.u : S) ^ n * ((C.u⁻¹ : Sˣ) : S) ^ n * a = a := by
    rw [← mul_pow, Units.mul_inv, one_pow, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, ← mul_assoc]
  · rw [Units.mul_inv, one_mul]
  all_goals exact h _ _

/-- A point `(x, y)` satisfies the Weierstrass equation of `C • W` if and only if
`(u²x + r, u³y + u²sx + t)` satisfies the Weierstrass equation of `W`. -/
theorem Affine.equation_variableChange_iff (x y : S) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation ((C.u : S) ^ 2 * x + C.r)
        ((C.u : S) ^ 3 * y + (C.u : S) ^ 2 * C.s * x + C.t) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := u_pow_mul_variableChange_a W C
  rw [Affine.equation_iff', Affine.equation_iff', ← (C.u ^ 6).isUnit.mul_right_eq_zero,
    Units.val_pow_eq_pow_val]
  congr! 1
  linear_combination (C.u : S) ^ 5 * x * y * h₁ + (C.u : S) ^ 3 * y * h₃ -
    (C.u : S) ^ 4 * x ^ 2 * h₂ - (C.u : S) ^ 2 * x * h₄ - h₆

/-- A point `(x, y)` is a nonsingular point of `C • W` if and only if `(u²x + r, u³y + u²sx + t)`
is a nonsingular point of `W`. -/
theorem Affine.nonsingular_variableChange_iff (x y : S) :
    (C • W).toAffine.Nonsingular x y ↔
      W.toAffine.Nonsingular ((C.u : S) ^ 2 * x + C.r)
        ((C.u : S) ^ 3 * y + (C.u : S) ^ 2 * C.s * x + C.t) := by
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := u_pow_mul_variableChange_a W C
  rw [Affine.Nonsingular, Affine.Nonsingular, Affine.equation_variableChange_iff,
    Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, Affine.evalEval_polynomialX,
    Affine.evalEval_polynomialY]
  refine and_congr_right fun _ ↦ ?_
  set X := (C.u : S) ^ 2 * x + C.r
  set Y := (C.u : S) ^ 3 * y + (C.u : S) ^ 2 * C.s * x + C.t
  have hX : (C.u : S) ^ 4 * ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄)) =
      W.a₁ * Y - (3 * X ^ 2 + 2 * W.a₂ * X + W.a₄) + C.s * (2 * Y + W.a₁ * X + W.a₃) := by
    linear_combination (C.u : S) ^ 3 * y * h₁ - 2 * (C.u : S) ^ 2 * x * h₂ - h₄
  have hY : (C.u : S) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) = 2 * Y + W.a₁ * X + W.a₃ := by
    linear_combination (C.u : S) ^ 2 * x * h₁ + h₃
  have hu (n : ℕ) (a : S) : (C.u : S) ^ n * a = 0 ↔ a = 0 := by
    rw [← Units.val_pow_eq_pow_val, Units.mul_right_eq_zero]
  rw [← not_iff_not, not_or, not_or, not_not, not_not, not_not, not_not, ← hu 4 (_ - _),
    ← hu 3 (_ + _ + _), hX, hY]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨by rwa [h', mul_zero, add_zero] at h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨by rw [h, h', mul_zero, add_zero], h'⟩

/-- The bijection between the affine points of `C • W` and those of `W` given by the change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
private def pointEquivOfVariableChange : (C • W).toAffine.Point ≃ W.toAffine.Point where
  toFun
    | .zero => .zero
    | .some x y h => .some _ _ ((Affine.nonsingular_variableChange_iff W C x y).mp h)
  invFun
    | .zero => .zero
    | .some x y h => .some (((C.u⁻¹ : Sˣ) : S) ^ 2 * (x - C.r))
        (((C.u⁻¹ : Sˣ) : S) ^ 3 * (y - C.s * (x - C.r) - C.t))
        ((Affine.nonsingular_variableChange_iff W C _ _).mpr <| by
          have hu := C.u.mul_inv
          convert h using 1 <;>
            [linear_combination ((C.u : S) * ↑C.u⁻¹ + 1) * (x - C.r) * hu;
            linear_combination (((C.u : S) * ↑C.u⁻¹) ^ 2 + (C.u : S) * ↑C.u⁻¹ + 1) *
              (y - C.s * (x - C.r) - C.t) * hu + ((C.u : S) * ↑C.u⁻¹ + 1) * C.s * (x - C.r) * hu])
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · have hu := C.u.mul_inv
      simp only [Affine.Point.some.injEq]
      constructor
      · linear_combination ((C.u : S) * ↑C.u⁻¹ + 1) * x * hu
      · linear_combination (((C.u : S) * ↑C.u⁻¹) ^ 2 + (C.u : S) * ↑C.u⁻¹ + 1) * y * hu
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · have hu := C.u.mul_inv
      simp only [Affine.Point.some.injEq]
      constructor
      · linear_combination ((C.u : S) * ↑C.u⁻¹ + 1) * (x - C.r) * hu
      · linear_combination (((C.u : S) * ↑C.u⁻¹) ^ 2 + (C.u : S) * ↑C.u⁻¹ + 1) *
          (y - C.s * (x - C.r) - C.t) * hu + ((C.u : S) * ↑C.u⁻¹ + 1) * C.s * (x - C.r) * hu

/-- A change of variables does not change the number of affine points. -/
theorem Affine.natCard_point_variableChange :
    Nat.card (C • W).toAffine.Point = Nat.card W.toAffine.Point :=
  Nat.card_congr (pointEquivOfVariableChange W C)

end VariableChange

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K}

/-- A Weierstrass equation with good reduction has a unit discriminant in its integral model. -/
private lemma isUnit_integralModel_Δ [W.HasGoodReduction R] : IsUnit (W.integralModel R).Δ := by
  have := (hasGoodReduction_iff_isElliptic_reduction R).mp ‹_›
  have h := (W.reduction R).isUnit_Δ
  rw [reduction, map_Δ] at h
  exact isUnit_of_map_unit (IsLocalRing.residue R) _ h

/-- An element of `K` with a power in `R` lies in `R`, since `R` is integrally closed. -/
private lemma exists_algebraMap_eq_of_pow_eq {n : ℕ} (hn : n ≠ 0) {c : R} {z : K}
    (hz : z ^ n = algebraMap R K c) : ∃ a : R, algebraMap R K a = z :=
  IsIntegrallyClosed.isIntegral_iff.mp
    ⟨Polynomial.X ^ n - Polynomial.C c, Polynomial.monic_X_pow_sub_C c hn, by simp [hz]⟩

/-- If `W` is integral and its discriminant has valuation `1`, then the reduction of the minimal
model `W.minimal R` has as many points as the reduction of `W` itself. -/
theorem natCard_point_reduction_minimal_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) :
    Nat.card ((W.minimal R).reduction R).toAffine.Point =
      Nat.card ((W.integralModel R).map (IsLocalRing.residue R)).toAffine.Point := by
  have := hasGoodReduction_of_valuation_Δ_eq_one R h
  have := hasGoodReduction_minimal_of_valuation_Δ_eq_one R h
  set C₀ := (W.exists_isMinimal R).choose
  have hC₀ : C₀ • W = W.minimal R := rfl
  obtain ⟨D₀, hD₀⟩ := isUnit_integralModel_Δ R (W := W)
  obtain ⟨D₁, hD₁⟩ := isUnit_integralModel_Δ R (W := W.minimal R)
  have hΔ : algebraMap R K D₁ = ((C₀.u⁻¹ : Kˣ) : K) ^ 12 * algebraMap R K D₀ := by
    rw [hD₀, hD₁, integralModel_Δ_eq, integralModel_Δ_eq, ← hC₀, variableChange_Δ]
  have hu : (C₀.u : K) ^ 12 * (C₀.u⁻¹ : Kˣ) ^ 12 = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
  have hD (D : Rˣ) : algebraMap R K D * algebraMap R K ↑D⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_pow_eq R (n := 12) (by norm_num)
      (c := D₀ * ↑D₁⁻¹) (z := (C₀.u : K)) <| by
    rw [map_mul]
    linear_combination (-(C₀.u : K) ^ 12) * hD D₁ +
      (C₀.u : K) ^ 12 * algebraMap R K ↑D₁⁻¹ * hΔ + algebraMap R K D₀ * algebraMap R K ↑D₁⁻¹ * hu
  obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_pow_eq R (n := 12) (by norm_num)
      (c := D₁ * ↑D₀⁻¹) (z := ((C₀.u⁻¹ : Kˣ) : K)) <| by
    rw [map_mul]
    linear_combination (-((C₀.u⁻¹ : Kˣ) : K) ^ 12) * hD D₀ - algebraMap R K ↑D₀⁻¹ * hΔ
  have hab : a * b = 1 := IsFractionRing.injective R K <| by
    rw [map_mul, map_one, ha, hb, Units.mul_inv]
  obtain ⟨CR, hCR⟩ := variableChange_integral_of_u_integral hC₀
    (u := ⟨a, b, hab, by rwa [mul_comm]⟩) ha
  have hW₁ : (W.minimal R).integralModel R = CR • W.integralModel R := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective R K)
    change ((W.minimal R).integralModel R).baseChange K = (CR • W.integralModel R).map _
    rw [← map_variableChange]
    change _ = CR.baseChange K • (W.integralModel R).baseChange K
    rw [baseChange_integralModel_eq, baseChange_integralModel_eq, hCR, hC₀]
  rw [reduction, hW₁, ← map_variableChange, Affine.natCard_point_variableChange]

/-- If `W` is integral and its discriminant has valuation `1`, then the trace of Frobenius is
`q + 1 - N`, where `q` is the cardinality of the residue field and `N` is the number of points of
the reduction of `W` itself. -/
theorem localTrace_of_valuation_Δ_eq_one [IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) :
    W.localTrace R = (Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
      Nat.card ((W.integralModel R).map (IsLocalRing.residue R)).toAffine.Point := by
  rw [localTrace, natCard_point_reduction_minimal_of_valuation_Δ_eq_one R h]

end WeierstrassCurve
