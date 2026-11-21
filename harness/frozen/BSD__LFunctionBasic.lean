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
coefficient is `1`. Over `ℚ` it computes the coefficient of the L-function at a prime power `p ^ k`
as the `k`-th coefficient of the local power series at the place above `p`.
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
  sorry

end LocalField

section NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The L-function of a Weierstrass curve over a number field is a multiplicative arithmetic
function. -/
theorem isMultiplicative_LFunction : W.LFunction.IsMultiplicative := by
  sorry

/-- The first coefficient of the L-function of a Weierstrass curve over a number field is `1`. -/
theorem LFunction_apply_one : W.LFunction 1 = 1 := by
  sorry

end NumberField

section Rat

/-- The coefficient of the L-function of a Weierstrass curve over `ℚ` at a prime power `p ^ k` is
the `k`-th coefficient of the local power series at the place `v` corresponding to `p`. -/
theorem LFunction_apply_primesEquiv_pow (W : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (k : ℕ) :
    W.LFunction ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ k) =
      PowerSeries.coeff k
        ((W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)) := by
  sorry

end Rat

end WeierstrassCurve
