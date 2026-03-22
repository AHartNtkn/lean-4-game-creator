import Game.Metadata

World "FinTuples"
Level 13

Title "Composing Tuples with Functions"

Introduction "
# Transforming Tuples

A tuple `f : Fin 2 -> NN` assigns a number to each index.
A function `g : NN -> NN` transforms numbers. Their composition
`g circ f : Fin 2 -> NN` transforms the tuple by applying `g`
to each entry.

For example, if `f = ![1, 2]` and `g` doubles its input,
then `g circ f = ![2, 4]` — applying `g` to each entry.

This is the tuple analog of **map** for lists. It foreshadows
`Finset.image` in Phase 2, where you'll apply a function to every
element of a finite set.

**Strategy**: Use `ext` to reduce to pointwise equality, substitute
both formulas, then verify each index by case split.
"

/-- Composing a tuple with a function gives a new tuple. -/
Statement (f : Fin 2 → ℕ) (g : ℕ → ℕ)
    (hf : f = ![1, 2]) (hg : ∀ x, g x = x * 2) :
    g ∘ f = ![2, 4] := by
  Hint "Start with `ext ⟨v, hv⟩` to reduce to pointwise equality."
  ext ⟨v, hv⟩
  Hint "The goal has `(g comp f) ⟨v, hv⟩` on the left — the
  composition applied to the index. Use `rw [Function.comp_apply]`
  to unfold this to `g (f ⟨v, hv⟩)`, then substitute both
  formulas with `rw [hf, hg]`."
  Hint (hidden := true) "Try `rw [Function.comp_apply, hf, hg]` as
  a single rewrite chain."
  rw [Function.comp_apply, hf, hg]
  Hint "Now case-split on `v` to verify each index."
  cases v with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ k => exact absurd hv (by omega)

Conclusion "
Composing a tuple with a function gives a new tuple:
`g circ f = ![g (f 0), g (f 1)]`.

The proof used the same `ext` + case split pattern, but with
an extra step: unfolding the composition (`g circ f` means
`fun i => g (f i)`) and substituting both formulas.

**Why this matters**: In Phase 2, `Finset.image g s` applies a
function `g` to every element of a finite set `s`. The
composition `g circ f` is the tuple version of the same idea.
Understanding tuple transformation prepares you for set-level
transformations.
"

NewTheorem Function.comp_apply

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
