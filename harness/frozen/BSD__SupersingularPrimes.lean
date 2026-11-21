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

/-- If `p ≡ 2 mod 3`, the curve `y² = x³ + b` over `𝔽_p` with nonzero discriminant has exactly
`p + 1` points: cubing is a bijection of `𝔽_p`, so each `y` determines one `x`. -/
theorem Affine.natCard_point_of_mod_three_eq_two (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (b : ZMod p) (hΔ : (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0) :
    Nat.card (⟨0, 0, 0, 0, b⟩ : WeierstrassCurve (ZMod p)).toAffine.Point = p + 1 := by
  sorry

/-- The L-function of `y² = x³ + b` over `ℚ` has `a_p = 0` at every prime `p ≡ 2 mod 3` with
`p ≠ 2` and `p ∤ b`. -/
theorem LFunction_apply_of_mod_three_eq_two (b : ℤ) (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b) :
    ((⟨0, 0, 0, 0, b⟩ : WeierstrassCurve ℤ).baseChange ℚ).LFunction p = 0 := by
  sorry

/-- The L-function of `y² = x³ + b` over `ℚ` has `a_{p²} = -p` at every prime `p ≡ 2 mod 3` with
`p ≠ 2` and `p ∤ b`. -/
theorem LFunction_apply_sq_of_mod_three_eq_two (b : ℤ) (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b) :
    ((⟨0, 0, 0, 0, b⟩ : WeierstrassCurve ℤ).baseChange ℚ).LFunction (p ^ 2) = -p := by
  sorry

/-- If `p ≡ 3 mod 4`, the curve `y² = x³ + a x` over `𝔽_p` with nonzero discriminant has exactly
`p + 1` points: `-1` is not a square, so `x` and `-x` together contribute two points. -/
theorem Affine.natCard_point_of_mod_four_eq_three (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (a : ZMod p) (hΔ : (⟨0, 0, 0, a, 0⟩ : WeierstrassCurve (ZMod p)).Δ ≠ 0) :
    Nat.card (⟨0, 0, 0, a, 0⟩ : WeierstrassCurve (ZMod p)).toAffine.Point = p + 1 := by
  sorry

/-- The L-function of `y² = x³ + a x` over `ℚ` has `a_p = 0` at every prime `p ≡ 3 mod 4` with
`p ∤ a`. -/
theorem LFunction_apply_of_mod_four_eq_three (a : ℤ) (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (ha : ¬ (p : ℤ) ∣ a) :
    ((⟨0, 0, 0, a, 0⟩ : WeierstrassCurve ℤ).baseChange ℚ).LFunction p = 0 := by
  sorry

end WeierstrassCurve

namespace FermatCubic

/-- The L-function of the Fermat cubic `y² = x³ - 432` has `a_p = 0` at every prime
`p ≡ 2 mod 3` with `p ≠ 2`. -/
theorem LFunction_apply_of_mod_three_eq_two (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2)
    (hp2 : p ≠ 2) : E.LFunction p = 0 := by
  sorry

/-- Infinitely many prime coefficients of the L-function of the Fermat cubic vanish. -/
theorem infinite_setOf_prime_and_LFunction_eq_zero :
    {p : ℕ | p.Prime ∧ E.LFunction p = 0}.Infinite := by
  sorry

/-- The coefficient `a_7` of the L-function of the Fermat cubic is `-1`. -/
theorem LFunction_apply_seven : E.LFunction 7 = -1 := by
  sorry

/-- The coefficient `a_13` of the L-function of the Fermat cubic is `5`. -/
theorem LFunction_apply_thirteen : E.LFunction 13 = 5 := by
  sorry

end FermatCubic
