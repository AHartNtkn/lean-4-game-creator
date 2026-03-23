import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 20

Title "Boss: Transpose of a Shifted Diagonal"

Introduction "
# Boss: Transpose of a Shifted Diagonal

You have a complete matrix toolkit:

| Tool | What it does |
|------|-------------|
| `ext i j` | proves matrix equality entry-wise |
| `Matrix.transpose_apply` | swaps indices: `Mᵀ i j = M j i` |
| `Matrix.add_apply` | splits a sum: `(M + N) i j = M i j + N i j` |
| `Matrix.diagonal_apply_eq` | on-diagonal: `(diagonal d) i i = d i` |
| `Matrix.diagonal_apply_ne` | off-diagonal: `i != j -> (diagonal d) i j = 0` |
| `eq_or_ne i j` | case split: `i = j` or `i != j` |
| `h.symm` | flips `i != j` to `j != i` |

Now prove a single result that requires all these tools to interact:

$$(\\text{diagonal}\\,d + N)^T = \\text{diagonal}\\,d + N^T$$

Adding a diagonal matrix `diagonal d` to an arbitrary matrix `N`
and then transposing is the same as adding `diagonal d` to the
transpose of `N`. The diagonal part is symmetric (does not change
under transpose), while the arbitrary part transposes normally.

This requires planning: you must reduce both sides to entries,
then handle the diagonal part (which needs a case split) and
the arbitrary part (which does not) in a single coordinated proof.
"

/-- The transpose of a diagonal plus an arbitrary matrix. -/
Statement (d : Fin 3 → ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ) :
    (diagonal d + N)ᵀ = diagonal d + Nᵀ := by
  Hint "Two matrices are equal entry-wise. Start with `ext i j`."
  Hint (hidden := true) "Try `ext i j`."
  ext i j
  Hint "Now simplify both sides using the entry-level lemmas.
  Use `transpose_apply` to peel the outer transpose, then
  `add_apply` to expand each sum, then `transpose_apply` again
  to simplify `Nᵀ i j`."
  Hint (hidden := true) "Try
  `rw [Matrix.transpose_apply, Matrix.add_apply, Matrix.add_apply, Matrix.transpose_apply]`.
  After these four rewrites, the goal reduces to
  `(diagonal d) j i + N j i = (diagonal d) i j + N j i`."
  rw [transpose_apply, add_apply, add_apply, transpose_apply]
  Hint "The `N j i` terms match on both sides. The challenge is
  showing `(diagonal d) j i = (diagonal d) i j`. This depends on
  whether `i = j` or `i != j`. Split into cases."
  Hint (hidden := true) "Try `obtain rfl | h := eq_or_ne i j`."
  obtain rfl | h := eq_or_ne i j
  -- i = j case
  · Hint "With `j` replaced by `i`, both sides are identical."
    rfl
  -- i ≠ j case
  · Hint "You have `h : i != j`. The left side has `(diagonal d) j i`
    — to show this is `0`, you need `j != i`, which is `h.symm`.
    The right side has `(diagonal d) i j` — use `h` directly."
    Hint (hidden := true) "Try
    `rw [Matrix.diagonal_apply_ne d h.symm, Matrix.diagonal_apply_ne d h]`."
    rw [diagonal_apply_ne d h.symm, diagonal_apply_ne d h]

Conclusion "
You proved that the transpose distributes over `diagonal d + N` in
a way that leaves the diagonal part unchanged. The proof required
genuine integration of five tools:

1. **`ext i j`** — reduced matrix equality to entry equality
2. **`transpose_apply`** and **`add_apply`** — simplified both sides
   to raw entries via the peel strategy
3. **`eq_or_ne i j`** — split into diagonal vs. off-diagonal cases,
   because the diagonal part behaves differently
4. **`h.symm`** — flipped the inequality direction to match the
   swapped indices left over from the transpose

No tool worked in isolation. The transpose created swapped indices
that required the case split; the case split needed `h.symm` because
of the specific index order left by the transpose. This is the kind
of reasoning you will do constantly in matrix proofs: reduce to entries,
handle the diagonal and off-diagonal cases separately, and track
how operations rearrange the indices.

**The big picture**: Matrices in Lean are functions. All matrix reasoning
reduces to function reasoning — accessing entries, proving entry-wise
equality, and tracking how operations (transpose, diagonal, addition)
affect individual entries. There is no magic; every matrix fact is a
statement about indices.

The entry-wise reasoning and big-operator skills from this world will
reappear in the counting and capstone worlds, where matrices over finite
index types connect to combinatorial identities and enumeration problems.
"

/-- `Fin.forall_fin_two` allows case enumeration on `Fin 2`.
Disabled so you use `eq_or_ne` instead of enumeration. -/
TheoremDoc Fin.forall_fin_two as "Fin.forall_fin_two" in "Fin"

/-- `Fin.forall_fin_one` allows case enumeration on `Fin 1`.
Disabled so you use `eq_or_ne` instead of enumeration. -/
TheoremDoc Fin.forall_fin_one as "Fin.forall_fin_one" in "Fin"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diagonal_transpose Matrix.diag_diagonal Matrix.diag_transpose Fin.forall_fin_two Fin.forall_fin_one Matrix.transpose_add Matrix.diagonal_add Matrix.diagonal_apply
