import Game.Metadata

World "PsetFin"
Level 5

Title "From Formula to Tuple"

Introduction "
# Identifying a Tuple from a Formula

You're given a tuple `f` described by a pointwise formula:
`f i = i.val + 1` for all `i : Fin 3`. Your job is to prove
that this completely determines the tuple as `![1, 2, 3]`, and
that you can compute `f` at the last index using the formula
and `Fin.val_last`.

**Part 1** tests the ext + case split pattern from FinTuples.

**Part 2** tests rewriting with a universally quantified hypothesis
and a navigation val lemma.
"

/-- A tuple described by a formula equals the explicit vec, and its last value is computable. -/
Statement (f : Fin 3 → ℕ) (h : ∀ i : Fin 3, f i = i.val + 1) :
    f = ![1, 2, 3] ∧ f (Fin.last 2) = 3 := by
  Hint "Split the conjunction, then handle each part."
  constructor
  -- Part 1: f = ![1, 2, 3]
  · Hint "Show the functions agree index by index using ext,
    then substitute the formula and case-split."
    ext ⟨v, hv⟩
    Hint (hidden := true) "`rw [h]` substitutes the formula, then
    case-split: `cases v with | zero => rfl | succ n => ...`"
    rw [h]
    cases v with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ m =>
        cases m with
        | zero => rfl
        | succ k => exact absurd hv (by omega)
  -- Part 2: f (Fin.last 2) = 3
  · Hint "Rewrite with the formula, then simplify `Fin.last 2`'s value."
    Hint (hidden := true) "`rw [h, Fin.val_last]`"
    rw [h, Fin.val_last]

Conclusion "
Two proof strategies for the price of one:

**Part 1** — The ext + case split + rfl pattern handles concrete
tuple identification. After `rw [h]`, each case reduces to a
numerical equality that `rfl` verifies by computation.

**Part 2** — Rewriting with a universally quantified hypothesis
(`rw [h]`) followed by a val lemma (`rw [Fin.val_last]`)
computes function values at navigation landmarks. This pattern
generalizes: for any `f` described by a formula, you can
compute `f` at `Fin.last`, `castSucc`, or `succ` by chaining
the formula rewrite with the appropriate val lemma.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
