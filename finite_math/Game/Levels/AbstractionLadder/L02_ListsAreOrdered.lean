import Game.Metadata

World "AbstractionLadder"
Level 2

Title "Lists Are Ordered"

Introduction "
# Lists Care About Order

Two lists with the same elements in different positions are **not**
equal. `[1, 2]` and `[2, 1]` contain the same elements, but in
a different order — so as lists, they are different objects.

This is a fundamental property of lists: the position of each element
is part of the list's identity.

To prove `[1, 2] ≠ [2, 1]`, we assume `[1, 2] = [2, 1]` and derive
a contradiction. If two lists built with `::` (cons) are equal, then
their heads must be equal and their tails must be equal. So
`[1, 2] = [2, 1]` would force `1 = 2` — which is absurd.

**Your task**: Prove that `[1, 2] ≠ [2, 1]`.
"

/-- Lists with the same elements in different order are not equal. -/
Statement : ([1, 2] : List ℕ) ≠ [2, 1] := by
  Hint "To prove `≠`, assume the equality and derive a contradiction.
  Use `intro h` to assume `[1, 2] = [2, 1]`."
  intro h
  Hint "The hypothesis `h : [1, 2] = [2, 1]` says `1 :: [2] = 2 :: [1]`.
  If two cons'd lists are equal, their heads must be equal.
  Use `injection h with h1 h2` to extract `h1 : 1 = 2` and `h2 : [2] = [1]`."
  Hint (hidden := true) "Try `injection h with h1 h2` to extract that
  the heads are equal (1 = 2)."
  injection h with h1 h2
  Hint "Now `h1 : 1 = 2` is in your context. This is absurd — use `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
Order matters in lists. `[1, 2]` and `[2, 1]` have the same elements
but are **not** equal because the elements appear in different positions.

This is precisely why we need `List.Perm` — a separate relation that
says 'these lists have the same elements, just rearranged.' Since list
equality is too strict (it cares about order), permutation gives us a
way to express 'same elements, any order.'

The proof technique you used:
1. `intro h` — assume the equality
2. `injection h with h1 h2` — extract that heads and tails must match
3. `omega` — the head equality `1 = 2` is absurd

`injection` works on any constructor equality: if `C a₁ a₂ = C b₁ b₂`,
then `a₁ = b₁` and `a₂ = b₂`.
"

/-- `injection` extracts equalities from constructor equalities.

If `h : C a₁ a₂ = C b₁ b₂` where `C` is a constructor (like `List.cons`
or `Option.some`), then `injection h with h1 h2` gives `h1 : a₁ = b₁`
and `h2 : a₂ = b₂`.

## Syntax
```
injection h with h1 h2
```

## When to use it
When you have an equality between two values built with the same
constructor and need to extract that the arguments are equal.

## Example
From `h : 1 :: [2] = 2 :: [1]`, `injection h with h1 h2` gives
`h1 : 1 = 2` and `h2 : [2] = [1]`.
-/
TacticDoc injection

TheoremTab "List"
NewTactic injection

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith contradiction
