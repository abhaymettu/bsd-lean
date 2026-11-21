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
  sorry

variable (W₀ : WeierstrassCurve ℤ) (v : HeightOneSpectrum (𝓞 ℚ))

/-- If `p` does not divide the discriminant of a Weierstrass curve `W₀` over `ℤ`, then Mathlib's
minimal model of `W₀` over the completion of `ℚ` at the place `v` above `p` has good
reduction. -/
theorem hasGoodReduction_minimal_baseChange_of_not_dvd
    (h : ¬ ((primesEquiv v : ℕ) : ℤ) ∣ W₀.Δ) :
    (((W₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ) := by
  sorry

/-- The coefficient `a_p` of the L-function of an elliptic curve over `ℚ` at a prime `p` of good
reduction of an integral model `W₀`: `a_p = p + 1 - |W₀(𝔽_p)|`. -/
theorem LFunction_baseChange_apply_of_not_dvd (p : ℕ) [Fact p.Prime] (h : ¬ (p : ℤ) ∣ W₀.Δ) :
    (W₀.baseChange ℚ).LFunction p =
      p + 1 - Nat.card (W₀.baseChange (ZMod p)).toAffine.Point := by
  sorry

/-- The Hecke recursion at a prime `p` of good reduction of an integral model `W₀`:
`a_{p^(n+2)} = a_p * a_{p^(n+1)} - p * a_{p^n}`. -/
theorem LFunction_baseChange_apply_pow_add_two_of_not_dvd (p : ℕ) [Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ W₀.Δ) (n : ℕ) :
    (W₀.baseChange ℚ).LFunction (p ^ (n + 2)) =
      (W₀.baseChange ℚ).LFunction p * (W₀.baseChange ℚ).LFunction (p ^ (n + 1)) -
        p * (W₀.baseChange ℚ).LFunction (p ^ n) := by
  sorry

end WeierstrassCurve
