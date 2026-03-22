import Game.Metadata

World "BinomialTheorem"
Level 6

Title "Flipping an Equation"

Introduction "
# Flipping an Equality with `.symm`

In the next few levels, you will derive identities from the binomial
theorem using the **specialize-simplify-rewrite** pattern. The final
step always produces a hypothesis `h` with the equation in one
direction, but the goal has it in the other.

For example, the row sum identity might give you
`h : 2 ^ n = ∑ choose n m`, but the goal is
`∑ choose n m = 2 ^ n` — the same equation, sides swapped.

The dot notation `h.symm` calls `Eq.symm` on `h`, producing a proof
of `b = a` from `h : a = b`. It flips the two sides of an equality.

**Your task**: You are given the row sum identity in one direction.
Close the goal, which has the sides swapped.

**Note**: `rw` is disabled for this level so you practice using
`.symm` directly.
"

/-- Flip the row sum identity. -/
Statement (n : ℕ) (h : 2 ^ n = ∑ m ∈ Finset.range (n + 1), Nat.choose n m) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose n m = 2 ^ n := by
  Hint "The goal is `∑ choose n m = 2 ^ n` and `h` says
  `2 ^ n = ∑ choose n m`. The sides are swapped. Use `exact h.symm`
  to flip `h` and close the goal."
  Hint (hidden := true) "Try `exact h.symm`."
  exact h.symm

Conclusion "
One step: `exact h.symm`.

**`.symm`** is dot notation for `Eq.symm`. If `h : a = b`, then
`h.symm : b = a`. It flips the two sides of an equality.

You will use this pattern repeatedly in the upcoming levels: the
specialize-simplify-rewrite method produces an equation `h : LHS = RHS`,
but the goal often has `RHS = LHS`. The final step is always
`exact h.symm`.
"

/-- `Eq.symm` flips an equality: if `h : a = b`, then `h.symm : b = a`.

The dot notation `h.symm` is the most common way to use this.

## Syntax
```
exact h.symm
```

## When to use it
When you have `h : a = b` but the goal needs `b = a` — the same
equation with the two sides swapped. This comes up constantly in
the specialize-simplify-rewrite pattern: the specialization produces
`h : LHS = RHS`, but the goal is `RHS = LHS`.

## Example
```
-- Given h : a = b, goal is b = a
exact h.symm
```
-/
TheoremDoc Eq.symm as "Eq.symm" in "Logic"

TheoremTab "Choose"
NewTheorem Eq.symm

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf omega linarith nlinarith rw
DisabledTheorem Nat.sum_range_choose
