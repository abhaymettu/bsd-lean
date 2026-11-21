/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import Mathlib

/-!
# The Mordell-Weil group of the Fermat cubic

The Fermat cubic `u³ + v³ = 1` has the Weierstrass model `E : y² = x³ - 432`, an elliptic curve over `ℚ`
of conductor 27. Using Fermat's Last Theorem for exponent 3 (`fermatLastTheoremThree`), we determine all
rational points of `E` and its group of rational points.

## Main results

* `FermatCubic.eq_or_eq_of_cube_add_cube_eq_one`: the rational solutions of `u³ + v³ = 1` are `(1, 0)`
  and `(0, 1)`.
* `FermatCubic.eq_of_sq_eq`: the affine rational points of `y² = x³ - 432` are `(12, 36)` and `(12, -36)`.
* `FermatCubic.natCard_point`: `E(ℚ)` has exactly three elements.
* `FermatCubic.nonempty_point_addEquiv_zmod`: `E(ℚ) ≃+ ZMod 3`.
* `FermatCubic.finrank_point`: `E(ℚ)` has rank `0`.
-/

namespace FermatCubic

open WeierstrassCurve

/-- The elliptic curve `y² = x³ - 432` over `ℚ`, a Weierstrass model of the Fermat cubic `u³ + v³ = 1`. -/
def E : Affine ℚ := ⟨0, 0, 0, 0, -432⟩

theorem isElliptic : E.IsElliptic := by
  sorry

theorem equation_iff (x y : ℚ) : E.Equation x y ↔ y ^ 2 = x ^ 3 - 432 := by
  sorry

/-- The rational points of the Fermat cubic `u³ + v³ = 1` are `(1, 0)` and `(0, 1)`. -/
theorem eq_or_eq_of_cube_add_cube_eq_one {u v : ℚ} (h : u ^ 3 + v ^ 3 = 1) :
    u = 1 ∧ v = 0 ∨ u = 0 ∧ v = 1 := by
  sorry

/-- The affine rational points of `y² = x³ - 432` are `(12, 36)` and `(12, -36)`. -/
theorem eq_of_sq_eq {x y : ℚ} (h : y ^ 2 = x ^ 3 - 432) : x = 12 ∧ (y = 36 ∨ y = -36) := by
  sorry

/-- The group of rational points of `y² = x³ - 432` has exactly three elements. -/
theorem natCard_point : Nat.card E.Point = 3 := by
  sorry

/-- The group of rational points of `y² = x³ - 432` is cyclic of order three. -/
theorem nonempty_point_addEquiv_zmod : Nonempty (E.Point ≃+ ZMod 3) := by
  sorry

/-- The elliptic curve `y² = x³ - 432` has Mordell-Weil rank zero over `ℚ`. -/
theorem finrank_point : Module.finrank ℤ E.Point = 0 := by
  sorry

end FermatCubic
