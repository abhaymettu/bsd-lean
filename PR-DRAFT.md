# Draft: how this would go to Mathlib

Nothing here has been submitted. This file is the plan and the pull request text, for the day it is.

## Before opening anything

1. Read Mathlib's current contribution guide, including its rules on AI-written code, and follow
   them. These proofs were written by Claude models. Say so in every pull request, and be ready to
   explain each proof to a reviewer.
2. Post in the Lean Zulip `#mathlib4` stream first: the L-function definitions were added by
   GitHub user `tb65536` in pull request #37771, and the natural question is what API he and the other
   elliptic curve maintainers want next. Small pull requests that match their plan will be reviewed
   faster than a large one that does not.
3. Coordinate with [TauCeti](https://github.com/TauCetiProject/TauCeti). It already has
   `isMultiplicative_localEulerFactor`, `isMultiplicative_LFunction`, `LFunction_apply_one`,
   `isMinimal_of_valuation_Δ_eq_one`, the local polynomial by reduction type, the point count under a
   change of variables over a field, and good reduction away from the discriminant over a Dedekind
   domain (checked at commit `84d74ced`, 2026-11-21). If its authors are upstreaming those, build on
   their pull requests and do not duplicate them. Re-check TauCeti on the day.
4. Rebase on Mathlib master. The files compile against tag `v4.36.0`. Mathlib files use the module
   system (`module` header, `public import` of the exact files needed, not `import Mathlib`); convert
   each file and minimise its imports.

## The split

Five small pull requests, in dependency order. Sizes are the current line counts with docstrings.

| # | Title | From | To (Mathlib path) | Lines |
|---|---|---|---|---|
| 1 | `feat(AlgebraicGeometry/EllipticCurve/LFunction): basic API for the local factor` | `BSD/LocalFactor.lean`, first half of `BSD/LFunctionBasic.lean` | `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean` | about 200 |
| 2 | `feat(AlgebraicGeometry/EllipticCurve/Reduction): good reduction from a unit discriminant` | `BSD/GoodReduction.lean` | `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` | about 110 |
| 3 | `feat(AlgebraicGeometry/EllipticCurve/Affine/Point): points under a change of variables` | `BSD/GoodReductionTrace.lean`, `Affine.natCard_point_map_ringEquiv` | `.../Affine/Point.lean` and `.../VariableChange.lean` | about 200 |
| 4 | `feat(AlgebraicGeometry/EllipticCurve/LFunction): coefficients of the L-function over ℚ` | rest of `BSD/LFunctionBasic.lean`, `BSD/LFunctionRat.lean`, `BSD/LFunctionRatIntegral.lean` | new file `.../EllipticCurve/LFunction/Rat.lean`; `card_residueField_adicCompletionIntegers` to `Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean` | about 350 |
| 5 | `feat: point counts of y² = x³ + b and y² = x³ + a x at supersingular primes` | general half of `BSD/SupersingularPrimes.lean` | new file under `.../EllipticCurve/` | about 180 |

`BSD/FermatCubic.lean` and the Fermat cubic half of `BSD/SupersingularPrimes.lean` are a worked
example, not library material. They fit Mathlib's `Archive/` as one file, "The Mordell-Weil group and
L-function coefficients of the Fermat cubic", once pull request 4 is merged.

Pull requests 1 and 2 overlap TauCeti the most. The parts with no known prior work are 4, 5 and the
Archive file, and 4 is the one that matters.

## Changes a reviewer will ask for

From an independent read of the statements:

- `localTrace` repeats the expression inside Mathlib's `localPolynomial`. Either refactor the
  definition to use it, or adopt TauCeti's `frobeniusTrace`.
- Rename `hasGoodReduction_minimal_iff`, for example to `hasGoodReduction_minimal_iff_exists_isIntegral`.
  TauCeti has a weaker lemma under the same name.
- The good reduction hypothesis `((W.baseChange (v.adicCompletion ℚ)).minimal
  (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)` is repeated in every
  statement of `LFunctionRat.lean`. Introduce an abbreviation for good reduction of `W` at `v`.
- Make the main declarations of pull request 3 equivalences of `Point` types, with the `Nat.card`
  statements as corollaries.
- Generalise the main theorem from `W₀ : WeierstrassCurve ℤ` to `W : WeierstrassCurve ℚ` with
  `[IsIntegral ℤ W]`, and ask whether the ℚ-specific results should be stated for number fields
  (TauCeti's good reduction lemma is over a Dedekind domain).
- `FermatCubic.finrank_point` is a corollary of `natCard_point`, and `Module.finrank` is also `0` for
  a module that is not finitely generated. Lead with `natCard_point` and
  `nonempty_point_addEquiv_zmod`.
- `FermatCubic.LFunction_apply_of_mod_three_eq_two` excludes `p = 2`. The coefficient is `0` at the
  bad primes `2` and `3` as well; that needs the additive reduction case and is not proved here.
- State congruence hypotheses the Mathlib way (`p ≡ 2 [MOD 3]` or `p % 3 = 2`, whichever the
  maintainers prefer), and tag the evident `simp` lemmas.

## Text for pull request 4

> This adds the first computation of coefficients of `WeierstrassCurve.LFunction`. Over `ℚ`, the
> value at `p ^ k` is the `k`-th coefficient of the local power series at the place above `p`. At a
> place of good reduction this gives `a_p = p + 1 - #W̃(𝔽_p)` and the recursion
> `a_{p^(n+2)} = a_p * a_{p^(n+1)} - p * a_{p^n}`; at places of split multiplicative, non-split
> multiplicative and additive reduction it gives `1`, `(-1) ^ k` and `0`. For a Weierstrass curve over
> `ℤ` and a prime not dividing its discriminant, the point count is that of the reduction of the given
> equation modulo `p`.
>
> The proofs were written with Claude and checked against Mathlib `v4.36.0`. Depends on #(1), #(2),
> #(3).

## How to check the source of this draft

`lake build && lake env lean Verify.lean` in this repository. The frozen statements are in
`harness/frozen/`.
