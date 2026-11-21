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

/-- The residue field of the ring of integers of the completion of `ℚ` at a finite place `v` has
cardinality the prime below `v`. -/
theorem card_residueField_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = primesEquiv v := by
  sorry

end Rat.HeightOneSpectrum

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))

/-- If `W` has good reduction at the place `v` above `p`, the coefficient `a_p` of the L-function
of `W` is the trace of Frobenius `p + 1 - |W̃(𝔽_p)|` of the reduction of a minimal model. -/
theorem LFunction_apply_primesEquiv_of_hasGoodReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    W.LFunction (primesEquiv v : ℕ) =
      (W.baseChange (v.adicCompletion ℚ)).localTrace (v.adicCompletionIntegers ℚ) := by
  sorry

/-- If `W` has good reduction at the place `v` above `p`, then `a_p = p + 1 - |W̃(𝔽_p)|`, where
`W̃` is the reduction of a minimal model of `W` over the completion at `v`. -/
theorem LFunction_apply_primesEquiv_eq_sub_natCard
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    W.LFunction (primesEquiv v : ℕ) = ((primesEquiv v : ℕ) : ℤ) + 1 -
      Nat.card (((W.baseChange (v.adicCompletion ℚ)).minimal
        (v.adicCompletionIntegers ℚ)).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point := by
  sorry

/-- The Hecke recursion: if `W` has good reduction at the place `v` above `p`, then
`a_{p^(n+2)} = a_p * a_{p^(n+1)} - p * a_{p^n}`. -/
theorem LFunction_apply_primesEquiv_pow_add_two
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) (n : ℕ) :
    W.LFunction ((primesEquiv v : ℕ) ^ (n + 2)) =
      W.LFunction (primesEquiv v : ℕ) * W.LFunction ((primesEquiv v : ℕ) ^ (n + 1)) -
        (primesEquiv v : ℕ) * W.LFunction ((primesEquiv v : ℕ) ^ n) := by
  sorry

/-- If `W` has split multiplicative reduction at the place `v` above `p`, then `a_{p^k} = 1`. -/
theorem LFunction_apply_primesEquiv_pow_of_hasSplitMultiplicativeReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        (v.adicCompletionIntegers ℚ))
    (k : ℕ) : W.LFunction ((primesEquiv v : ℕ) ^ k) = 1 := by
  sorry

/-- If `W` has non-split multiplicative reduction at the place `v` above `p`, then
`a_{p^k} = (-1) ^ k`. -/
theorem LFunction_apply_primesEquiv_pow_of_hasNonsplitMultiplicativeReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasMultiplicativeReduction (v.adicCompletionIntegers ℚ))
    (h' : ¬ ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        (v.adicCompletionIntegers ℚ))
    (k : ℕ) : W.LFunction ((primesEquiv v : ℕ) ^ k) = (-1) ^ k := by
  sorry

/-- If `W` has additive reduction at the place `v` above `p`, then `a_{p^k} = 0` for `k ≥ 1`. -/
theorem LFunction_apply_primesEquiv_pow_of_hasAdditiveReduction
    (h : ((W.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasAdditiveReduction (v.adicCompletionIntegers ℚ))
    {k : ℕ} (hk : k ≠ 0) : W.LFunction ((primesEquiv v : ℕ) ^ k) = 0 := by
  sorry

end WeierstrassCurve
