# Scan: `harness/examples/SquareZero.lean`

2026-11-21T14:49:49, prover `claude-batch --model sonnet`. 11 candidates, 11 exist in Mathlib (checked by `#check`), 0 not found. A scan proposes routes; it proves nothing. Only EXISTS rows are usable.

| name | in Mathlib | type (from `#check`) | area | how it would be used | to connect it |
|---|---|---|---|---|---|
| `Matrix.aeval_self_charpoly` | EXISTS | Matrix.aeval_self_charpoly.{u_1, u_4} {R : Type u_1} [CommRing R] {n : Type u_4} [DecidableEq n] [Fintype n] (M : Matrix n n R) : (Polynomial.aeval M) M.charpoly = 0 | LinearAlgebra/Cayley-Hamilton | Cayley-Hamilton gives A^2 - trace·A + det·1 = 0; combined with A*A = 0 this gives trace·A = det·1 | Rewrite the charpoly of a 2x2 matrix with charpoly_fin_two, evaluate it at A, and use h to get trace·A = det·1 for both the det and trace claims |
| `Matrix.charpoly_fin_two` | EXISTS | Matrix.charpoly_fin_two.{u} {R : Type u} [CommRing R] [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) : M.charpoly = Polynomial.X ^ 2 - Polynomial.C M.trace * Polynomial.X + Polynomial.C M.det | LinearAlgebra/Charpoly | Explicit charpoly X^2 - C(trace)·X + C(det), the input Cayley-Hamilton needs, and from it the trace_mul_self identity | Specialize to Fin 2 and combine with aeval_self_charpoly via map_sub, map_mul, and aeval_X |
| `Matrix.trace_eq_neg_charpoly_coeff` | EXISTS | Matrix.trace_eq_neg_charpoly_coeff.{u, v} {R : Type u} [CommRing R] {n : Type v} [DecidableEq n] [Fintype n] [Nonempty n] (M : Matrix n n R) : M.trace = -M.charpoly.coeff (Fintype.card n - 1) | LinearAlgebra/Charpoly | Read the trace off the charpoly's coefficient at degree card-1, tying trace to the charpoly of a nilpotent matrix | Show the charpoly of a square-zero matrix is X^2, so that coefficient vanishes |
| `Matrix.det_eq_sign_charpoly_coeff` | EXISTS | Matrix.det_eq_sign_charpoly_coeff.{u, v} {R : Type u} [CommRing R] {n : Type v} [DecidableEq n] [Fintype n] (M : Matrix n n R) : M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0 | LinearAlgebra/Charpoly | Read det off the constant coefficient of the charpoly, so a charpoly of X^2 forces det = 0 | Show the charpoly of a square-zero matrix has constant coefficient 0 |
| `IsNilpotent.eq_zero` | EXISTS | IsNilpotent.eq_zero.{u_3} {R : Type u_3} {x : R} [Zero R] [Pow R ℕ] [IsReduced R] (h : IsNilpotent x) : x = 0 | RingTheory/Nilpotent | Over a field (reduced ring), a nilpotent element is 0. Apply it to det A, since det A ^ 2 = 0 | Get det A ^ 2 = 0 from h via det_mul, then show IsNilpotent (det A) |
| `pow_eq_zero_iff` | EXISTS | pow_eq_zero_iff.{u_1} {M₀ : Type u_1} [MonoidWithZero M₀] {a : M₀} {n : ℕ} [IsReduced M₀] (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 | Algebra/GroupWithZero (NoZeroDivisors) | From det A * det A = 0 (or (det A)^2 = 0) conclude det A = 0 in a field | Rewrite det (A*A) = det A * det A = det 0 = 0 and get the power form, with 2 ≠ 0 as a natural number |
| `LinearMap.isNilpotent_trace_of_isNilpotent` | EXISTS | LinearMap.isNilpotent_trace_of_isNilpotent.{u_1, u_2} {R : Type u_1} [CommRing R] {M : Type u_2} [AddCommGroup M] [Module R M] {f : M →ₗ[R] M} (hf : IsNilpotent f) : IsNilpotent ((LinearMap.trace R M) f) | LinearAlgebra/Trace | Trace of a nilpotent endomorphism is nilpotent, hence 0 in a field | Pass from A to Matrix.toLin' A, show nilpotency from A*A = 0, then use IsNilpotent.eq_zero and LinearMap.trace_eq_matrix_trace |
| `Matrix.exists_mulVec_eq_zero_iff` | EXISTS | Matrix.exists_mulVec_eq_zero_iff.{u_1, u_4} {n : Type u_1} [Fintype n] {A : Type u_4} [CommRing A] [IsDomain A] {M : Matrix n n A} [DecidableEq n] : (∃ v, v ≠ 0 ∧ M.mulVec v = 0) ↔ M.det = 0 | LinearAlgebra/Matrix/Determinant (kernel/det criterion) | det A = 0 iff A has a nonzero kernel vector, and any nonzero column of A lies in the kernel when A*A = 0 | Case split on A = 0; otherwise pick a nonzero column v, show A *ᵥ v = 0 via mulVec and the product, then apply the iff |
| `Matrix.det_fin_two` | EXISTS | Matrix.det_fin_two.{v} {R : Type v} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 | LinearAlgebra/Matrix (own area) | Expand det into a 0 0 * a 1 1 - a 0 1 * a 1 0 for the trace_mul_self identity | Expand A*A entrywise and trace via trace_fin_two, then finish with ring |
| `Matrix.trace_fin_two` | EXISTS | Matrix.trace_fin_two.{u_6} {R : Type u_6} [AddCommMonoid R] (A : Matrix (Fin 2) (Fin 2) R) : A.trace = A 0 0 + A 1 1 | LinearAlgebra/Matrix (own area) | Trace as a 0 0 + a 1 1, used for entrywise computation of (A*A).trace | Combine with mul_apply, Fin.sum_univ_two and det_fin_two, then ring |
| `Matrix.det_mul` | EXISTS | Matrix.det_mul.{v, u_2} {n : Type u_2} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R] (M N : Matrix n n R) : (M * N).det = M.det * N.det | LinearAlgebra/Matrix (own area) | Multiplicativity of det turns A*A = 0 into det A * det A = 0 | Rewrite det (A*A) and det 0 for Fin 2 (nonempty index) to get det A ^ 2 = 0 |

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

namespace Matrix

variable {K : Type*} [Field K]

def IsSquareZero (A : Matrix (Fin 2) (Fin 2) K) : Prop :=
  A * A = 0

theorem trace_mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    (A * A).trace = A.trace ^ 2 - 2 * A.det := sorry
theorem IsSquareZero.det_eq_zero {A : Matrix (Fin 2) (Fin 2) K} (h : A.IsSquareZero) : A.det = 0 := sorry
theorem IsSquareZero.trace_eq_zero {A : Matrix (Fin 2) (Fin 2) K} (h : A.IsSquareZero) :
    A.trace = 0 := sorry
end Matrix
```
````

</details>
