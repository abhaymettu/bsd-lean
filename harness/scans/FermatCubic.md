# Scan: `BSD/FermatCubic.lean`

2026-11-21T14:49:14, prover `claude-batch --model sonnet`. 9 candidates, 8 exist in Mathlib (checked by `#check`), 1 not found. A scan proposes routes; it proves nothing. Only EXISTS rows are usable.

| name | in Mathlib | type (from `#check`) | area | how it would be used | to connect it |
|---|---|---|---|---|---|
| `fermatLastTheoremThree` | EXISTS | fermatLastTheoremThree : FermatLastTheoremFor 3 | Number theory (Fermat's Last Theorem) | Clear denominators in u^3+v^3=1 to get integer a^3+b^3=c^3, which forces abc=0, giving the two trivial solutions | Write u=a/c, v=b/c with a common denominator c≠0, cast to ℤ, and rule out the nonzero-case (a, b, c all nonzero) using the theorem |
| `FermatLastTheoremFor` | EXISTS | FermatLastTheoremFor (n : ℕ) : Prop | Number theory (Fermat's Last Theorem) | Statement form of the n=3 result, specialized to ℤ so it can be applied to a,b,c | Unfold it for exponent 3 and match the shape a^3+b^3=c^3 with the signs and zero cases handled |
| `isAddCyclic_of_prime_card` | EXISTS | isAddCyclic_of_prime_card.{u_1} {α : Type u_1} [AddGroup α] {p : ℕ} [hp : Fact (Nat.Prime p)] (h : Nat.card α = p) : IsAddCyclic α | Group theory (cyclic groups) | A finite additive group of prime order 3 is cyclic, which gives IsAddCyclic E.Point | Provide Fintype/Finite structure and Nat.card E.Point = 3 (natCard_point), with 3 prime |
| `num_dvd_of_is_root` | EXISTS | num_dvd_of_is_root.{u_1, u_2} {A : Type u_1} {K : Type u_2} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K] [Algebra A K] [IsFractionRing A K] {p : Polynomial A} {r : K} (hr : (Polynomial.aeval r) p = 0) : IsFractionRing.num A r ∣ p.coeff 0 | Commutative algebra (rational root theorem) | Bound the numerator and denominator of a rational x with y^2 = x^3-432 or of a rational root of an auxiliary cubic to reduce to finitely many cases | Build the polynomial over ℤ with the right leading coefficient and show the rational point's coordinate is a root of it |
| `Nat.card_congr` | EXISTS | Nat.card_congr.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α ≃ β) : Nat.card α = Nat.card β | Set theory (cardinality) | Transfer Nat.card E.Point to the cardinality of the explicit set {0, some (12,36), some (12,-36)} | Build an Equiv between E.Point and a 3-element type using eq_of_sq_eq and the Point.zero/some constructors |
| `Module.finite_of_finite` | EXISTS | Module.finite_of_finite.{u_1, u_2} (R : Type u_1) {M : Type u_2} [Semiring R] [AddCommMonoid M] [Module R M] [Finite R] [Module.Finite R M] : Finite M | Linear algebra (finite modules) | Show E.Point is a finite ℤ-module once it is a finite type, to start the rank computation for finrank_point | Supply Finite E.Point from natCard_point (nonzero Nat.card) and the Module ℤ E.Point instance on the additive group |
| `WeierstrassCurve.Affine.Point` | EXISTS | WeierstrassCurve.Affine.Point.{r} {R : Type r} [CommRing R] (W' : WeierstrassCurve.Affine R) : Type r | Elliptic curves (own area) | Gives the point type and its constructors zero and some, which are used to enumerate E.Point | Show that every affine point satisfies equation_iff and therefore has x=12, y=±36, so only three points exist |
| `WeierstrassCurve.Affine.Equation` | EXISTS | WeierstrassCurve.Affine.Equation.{r} {R : Type r} [CommRing R] (W : WeierstrassCurve.Affine R) (x y : R) : Prop | Elliptic curves (own area) | Unfold the membership condition to get equation_iff | Substitute a₁=a₂=a₃=a₄=0, a₆=-432 and normalize the ring equation with simp/ring |
| `zmodCyclicAddEquiv` | NOT FOUND | Unknown identifier `zmodCyclicAddEquiv` | Group theory (cyclic groups) | Turn a cyclic additive group of cardinality 3 into an additive equivalence with ZMod 3 | Show E.Point is additively cyclic, via a generator (the point (12,36)), and that its Nat.card is 3 |

<details><summary>Prompt sent to the prover</summary>

````
You are scouting proof routes for Lean 4 statements against Mathlib (Lean v4.36.0). Do not write a proof.

Strong proofs often come through a bridge: a result Mathlib already has in an area far from where the statement
itself lives, which carries most of the weight once the statement is connected to it. List candidate bridges.

Rules:
- at least 8 candidates, spread over at least 4 different areas of Mathlib; at most a third of them from the
  statement's own area;
- each name must be the exact fully qualified name of a theorem, lemma or definition in current Mathlib or Lean
  core. Every name is checked by Lean; a name that does not exist is worthless, so do not guess or invent names;
- prefer deep results (a named theorem, a classification, a counting formula) over routine simp lemmas.

Reply with one line per candidate and nothing else:
CANDIDATE: <fully qualified name> | <Mathlib area> | <one line: how it would be used> | <one line: what has to be shown to connect it>

## Statements
```lean
import Mathlib

namespace FermatCubic

open WeierstrassCurve

def E : Affine ℚ := ⟨0, 0, 0, 0, -432⟩

theorem isElliptic : E.IsElliptic := sorry
theorem equation_iff (x y : ℚ) : E.Equation x y ↔ y ^ 2 = x ^ 3 - 432 := sorry
theorem eq_or_eq_of_cube_add_cube_eq_one {u v : ℚ} (h : u ^ 3 + v ^ 3 = 1) :
    u = 1 ∧ v = 0 ∨ u = 0 ∧ v = 1 := sorry
theorem eq_of_sq_eq {x y : ℚ} (h : y ^ 2 = x ^ 3 - 432) : x = 12 ∧ (y = 36 ∨ y = -36) := sorry
theorem natCard_point : Nat.card E.Point = 3 := sorry
theorem nonempty_point_addEquiv_zmod : Nonempty (E.Point ≃+ ZMod 3) := sorry
theorem finrank_point : Module.finrank ℤ E.Point = 0 := sorry
end FermatCubic
```
````

</details>
