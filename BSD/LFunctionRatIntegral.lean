/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib
import BSD.LFunctionRat
import BSD.GoodReduction
import BSD.GoodReductionTrace

/-!
# The L-function of an elliptic curve over `ℚ` at primes of good reduction of an integral model

Let `W₀` be a Weierstrass curve over `ℤ` and let `p` be a prime not dividing its discriminant.
This file shows that the base change of `W₀` to `ℚ` has good reduction at the place above `p`
(for Mathlib's chosen minimal model over the completion), and deduces the textbook form of the
coefficients of the L-function at `p`: `a_p = p + 1 - |W₀(𝔽_p)|`, where `W₀(𝔽_p)` is the set of
points of the reduction of `W₀` modulo `p`, together with the Hecke recursion at `p`.

## Main results

* `WeierstrassCurve.hasGoodReduction_minimal_baseChange_of_not_dvd`: good reduction at `v` for an
  integral model whose discriminant is prime to `p`.
* `WeierstrassCurve.LFunction_baseChange_apply_of_not_dvd`: `a_p = p + 1 - |W₀(𝔽_p)|`.
* `WeierstrassCurve.LFunction_baseChange_apply_pow_add_two_of_not_dvd`: the Hecke recursion.
-/

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

namespace WeierstrassCurve

/-- A ring isomorphism of the base induces a bijection on the affine points, so it preserves
their number. -/
theorem Affine.natCard_point_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (e : R ≃+* S) :
    Nat.card (W.map (e : R →+* S)).toAffine.Point = Nat.card W.toAffine.Point := by
  rw [Nat.card_congr (Affine.nonsingularPointEquiv _),
    Nat.card_congr (Affine.nonsingularPointEquiv _)]
  exact Nat.card_congr (Equiv.optionCongr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv)
    fun xy ↦ (W.toAffine.map_nonsingular e.injective xy.1 xy.2).symm)).symm

variable (W₀ : WeierstrassCurve ℤ) (v : HeightOneSpectrum (𝓞 ℚ))

/-- Base changing a curve over `ℤ` to `ℚ` and then to `K_v` is the same as mapping it along the
cast `ℤ → K_v`. -/
private lemma baseChange_baseChange_adicCompletion :
    (W₀.baseChange ℚ).baseChange (v.adicCompletion ℚ) = W₀.map (Int.castRingHom _) := by
  rw [baseChange, baseChange, map_map]
  congr 1
  exact RingHom.ext_int _ _

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- A curve over `ℤ`, base changed to the completion `K_v`, is integral over `O_v`. -/
instance isIntegral_baseChange_baseChange_adicCompletion :
    IsIntegral (v.adicCompletionIntegers ℚ)
      ((W₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)) := by
  rw [baseChange_baseChange_adicCompletion]
  exact isIntegral_of_exists_lift (R := v.adicCompletionIntegers ℚ)
    ⟨W₀.a₁, map_intCast _ _⟩ ⟨W₀.a₂, map_intCast _ _⟩ ⟨W₀.a₃, map_intCast _ _⟩
    ⟨W₀.a₄, map_intCast _ _⟩ ⟨W₀.a₆, map_intCast _ _⟩

/-- If `p` does not divide the discriminant of `W₀`, the discriminant of `W₀` over `K_v` has
valuation `1`. -/
private lemma valuation_Δ_baseChange_eq_one (h : ¬ ((primesEquiv v : ℕ) : ℤ) ∣ W₀.Δ) :
    HeightOneSpectrum.valuation (v.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers ℚ))
      ((W₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).Δ = 1 := by
  have hu : IsUnit (W₀.Δ : v.adicCompletionIntegers ℚ) := by
    rw [← isUnit_map_iff (adicCompletionIntegers.padicIntEquiv v).toRingEquiv, map_intCast,
      PadicInt.isUnit_iff]
    exact (PadicInt.norm_le_one _).antisymm
      (not_lt.mp ((PadicInt.norm_int_lt_one_iff_dvd _).not.mpr h))
  rw [baseChange_baseChange_adicCompletion, map_Δ, eq_intCast, ← map_intCast
    (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))]
  refine (HeightOneSpectrum.valuation_le_one _ _).antisymm (not_lt.mp fun hlt ↦ ?_)
  exact (IsLocalRing.mem_maximalIdeal _).mp
    ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mp hlt) hu

/-- The integral model of `W₀` over `K_v` chosen by Mathlib is the base change of `W₀` to
`O_v`. -/
private lemma integralModel_baseChange_baseChange_adicCompletion :
    ((W₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).integralModel
      (v.adicCompletionIntegers ℚ) = W₀.baseChange (v.adicCompletionIntegers ℚ) := by
  apply WeierstrassCurve.map_injective
    (IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
  change (((W₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).integralModel
    (v.adicCompletionIntegers ℚ)).baseChange (v.adicCompletion ℚ) =
      (W₀.baseChange (v.adicCompletionIntegers ℚ)).baseChange (v.adicCompletion ℚ)
  rw [baseChange_integralModel_eq, baseChange_baseChange_adicCompletion, baseChange, baseChange,
    map_map]
  congr 1

/-- If `p` does not divide the discriminant of a Weierstrass curve `W₀` over `ℤ`, then Mathlib's
minimal model of `W₀` over the completion of `ℚ` at the place `v` above `p` has good
reduction. -/
theorem hasGoodReduction_minimal_baseChange_of_not_dvd
    (h : ¬ ((primesEquiv v : ℕ) : ℤ) ∣ W₀.Δ) :
    (((W₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ) :=
  hasGoodReduction_minimal_of_valuation_Δ_eq_one _ (valuation_Δ_baseChange_eq_one W₀ v h)

/-- The coefficient `a_p` of the L-function of an elliptic curve over `ℚ` at a prime `p` of good
reduction of an integral model `W₀`: `a_p = p + 1 - |W₀(𝔽_p)|`. -/
theorem LFunction_baseChange_apply_of_not_dvd (p : ℕ) [Fact p.Prime] (h : ¬ (p : ℤ) ∣ W₀.Δ) :
    (W₀.baseChange ℚ).LFunction p =
      p + 1 - Nat.card (W₀.baseChange (ZMod p)).toAffine.Point := by
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), (primesEquiv v : ℕ) = p :=
    ⟨primesEquiv.symm ⟨p, Fact.out⟩, congrArg Subtype.val (primesEquiv.apply_symm_apply _)⟩
  have h' : ¬ ((primesEquiv v : ℕ) : ℤ) ∣ W₀.Δ := hv ▸ h
  have key := LFunction_apply_primesEquiv_eq_sub_natCard _ v
    (hasGoodReduction_minimal_baseChange_of_not_dvd W₀ v h')
  rw [hv] at key
  rw [key, natCard_point_reduction_minimal_of_valuation_Δ_eq_one _
    (valuation_Δ_baseChange_eq_one W₀ v h'), integralModel_baseChange_baseChange_adicCompletion]
  let e : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod p :=
    ((IsLocalRing.ResidueField.mapEquiv (adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField).trans (ZMod.ringEquivCongr hv)
  have hW : W₀.baseChange (ZMod p) =
      ((W₀.baseChange (v.adicCompletionIntegers ℚ)).map
        (IsLocalRing.residue (v.adicCompletionIntegers ℚ))).map (e : _ →+* ZMod p) := by
    rw [baseChange, baseChange, map_map, map_map]
    congr 1
    exact RingHom.ext_int _ _
  rw [hW, Affine.natCard_point_map_ringEquiv]

/-- The Hecke recursion at a prime `p` of good reduction of an integral model `W₀`:
`a_{p^(n+2)} = a_p * a_{p^(n+1)} - p * a_{p^n}`. -/
theorem LFunction_baseChange_apply_pow_add_two_of_not_dvd (p : ℕ) [Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ W₀.Δ) (n : ℕ) :
    (W₀.baseChange ℚ).LFunction (p ^ (n + 2)) =
      (W₀.baseChange ℚ).LFunction p * (W₀.baseChange ℚ).LFunction (p ^ (n + 1)) -
        p * (W₀.baseChange ℚ).LFunction (p ^ n) := by
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), (primesEquiv v : ℕ) = p :=
    ⟨primesEquiv.symm ⟨p, Fact.out⟩, congrArg Subtype.val (primesEquiv.apply_symm_apply _)⟩
  have key := LFunction_apply_primesEquiv_pow_add_two _ v
    (hasGoodReduction_minimal_baseChange_of_not_dvd W₀ v (hv ▸ h)) n
  rwa [hv] at key

end WeierstrassCurve
