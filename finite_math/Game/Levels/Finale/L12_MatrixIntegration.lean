import Game.Metadata

open Matrix

World "Finale"
Level 12

Title "Trace of the Identity"

Introduction "
# The Identity Matrix Has Trace $n$

The **trace** of a square matrix is the sum of its diagonal
entries: $\\text{tr}(M) = \\sum_i M_{ii}$.

The identity matrix `diagonal (fun _ => 1)` has 1 on every
diagonal entry and 0 elsewhere. Its trace should be $n$ —
the number of 1s along the diagonal.

Prove this by combining matrix API (from the Matrices world)
with cardinality and big operator tools.

**The proof plan**:
1. Show each summand equals 1 using `diag_apply` and
   `diagonal_apply_eq`
2. Use `sum_congr rfl` to rewrite the sum
3. Compute `sum of 1s over Fin n` = $n$ using `sum_const`,
   `card_univ`, `card_fin`
"

/-- The trace of the identity matrix is n. -/
Statement (n : ℕ) :
    ∑ i ∈ (Finset.univ : Finset (Fin n)),
      diag (diagonal (fun _ : Fin n => (1 : ℕ))) i = n := by
  Hint "Each summand is `diag (diagonal (fun _ => 1)) i`. Use
  `sum_congr rfl` with a helper to show each summand equals 1."
  Hint (hidden := true) "Try:
  `have h : forall i in (Finset.univ : Finset (Fin n)), diag (diagonal (fun _ : Fin n => (1 : Nat))) i = 1 := by`
  `  intro i _`
  `  rw [diag_apply, diagonal_apply_eq]`"
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      diag (diagonal (fun _ : Fin n => (1 : ℕ))) i = 1 := by
    intro i _
    rw [diag_apply, diagonal_apply_eq]
  Hint "Rewrite the sum using your helper, then compute the
  constant sum."
  Hint (hidden := true) "Try:
  `rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`"
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]

Conclusion "
**Trace of the identity**: $\\text{tr}(I_n) = n$.

The proof combined tools from three phases:
- **Phase 6** (Matrices): `diag_apply` and `diagonal_apply_eq`
  to evaluate each diagonal entry
- **Phase 4** (Big operators): `sum_congr rfl` to rewrite
  the summands, `sum_const` to evaluate the constant sum
- **Phase 3** (Cardinality): `card_univ` and `card_fin` to
  compute $|\\text{Fin}\\,n| = n$

This result — `tr(I) = n` — is foundational in linear algebra.
The trace is the only matrix invariant that is both linear
(`tr(A + B) = tr(A) + tr(B)`) and cyclic (`tr(AB) = tr(BA)`).
Computing `tr(I) = n` is its simplest instance: the identity
matrix has $n$ ones on the diagonal.

**Tuple connection**: A matrix `M : Matrix (Fin m) (Fin n) alpha`
is a function `Fin m -> Fin n -> alpha` — literally a tuple of
tuples. The diagonal extraction `diag M i = M i i` selects the
$i$-th entry of the $i$-th row, connecting the matrix back to
the tuple indexing from Phase 1.
"

/-- `Matrix.diag_diagonal` proves `diag (diagonal d) = d` directly.
Disabled so you work through `diag_apply` and `diagonal_apply_eq`
step by step. -/
TheoremDoc Matrix.diag_diagonal as "Matrix.diag_diagonal" in "Matrix"

/-- `Matrix.diagonal_apply` gives the if-then-else form:
`(diagonal d) i j = if i = j then d i else 0`.
Disabled so you use the more explicit `diagonal_apply_eq` and
`diagonal_apply_ne` lemmas instead. -/
TheoremDoc Matrix.diagonal_apply as "Matrix.diagonal_apply" in "Matrix"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Prevent direct computation shortcuts
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_apply
