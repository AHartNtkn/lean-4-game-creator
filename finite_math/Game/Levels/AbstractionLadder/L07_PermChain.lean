import Game.Metadata

World "AbstractionLadder"
Level 7

Title "Chaining Permutations"

Introduction "
# Chaining Permutations with Trans

A single swap only moves adjacent elements. To rearrange elements
that are far apart, you chain multiple permutations using transitivity.

If you have `h₁ : l₁ ~ l₂` and `h₂ : l₂ ~ l₃`, then
`h₁.trans h₂ : l₁ ~ l₃`.

**Your task**: Prove that `[1, 2, 3] ~ [3, 1, 2]`.

**Strategy**: Find an intermediate list that connects the two.

One approach:
1. `[1, 2, 3] ~ [1, 3, 2]` — swap `2` and `3` in the tail
2. `[1, 3, 2] ~ [3, 1, 2]` — swap `1` and `3` at the front

Use `have` to create intermediate permutation facts, then chain
with `.trans`.
"

/-- A permutation requiring two swaps. -/
Statement : List.Perm [1, 2, 3] [3, 1, 2] := by
  Hint "Start by proving the first swap: `[1, 2, 3] ~ [1, 3, 2]`.
  The tail `[2, 3]` needs swapping, and the head `1` stays.
  Use `have h1 : List.Perm [1, 2, 3] [1, 3, 2] := ...`

  **Tip**: If the term-mode expression feels hard to type in one go,
  you can use `have h1 : List.Perm [1, 2, 3] [1, 3, 2] := by exact ...`
  to get intermediate feedback from the proof state."
  Hint (hidden := true) "The first step swaps in the tail:
  `have h1 : List.Perm [1, 2, 3] [1, 3, 2] := List.Perm.cons 1 (List.Perm.swap 3 2 [])`

  Alternatively, for intermediate feedback:
  `have h1 : List.Perm [1, 2, 3] [1, 3, 2] := by exact List.Perm.cons 1 (List.Perm.swap 3 2 [])`"
  have h1 : List.Perm [1, 2, 3] [1, 3, 2] := List.Perm.cons 1 (List.Perm.swap 3 2 [])
  Hint "Now prove the second swap: `[1, 3, 2] ~ [3, 1, 2]`.
  This swaps the first two elements."
  Hint (hidden := true) "The second step:
  `have h2 : List.Perm [1, 3, 2] [3, 1, 2] := List.Perm.swap 3 1 [2]`"
  have h2 : List.Perm [1, 3, 2] [3, 1, 2] := List.Perm.swap 3 1 [2]
  Hint "Now chain the two with `.trans`."
  Hint (hidden := true) "Try `exact h1.trans h2`."
  exact h1.trans h2

Conclusion "
You built a permutation by chaining two swaps through an intermediate
list. The pattern:

1. Find intermediate lists that differ by one swap
2. Prove each swap with `List.Perm.swap` (possibly wrapped in
   `List.Perm.cons` for shared heads)
3. Chain with `.trans`

A permutation preserves length: `List.Perm.length_eq` gives
`l₁.Perm l₂ → l₁.length = l₂.length`. This makes sense — rearranging
elements doesn't change how many there are.

**Algebraic structure**: Notice the three properties you've now seen:
- **Identity**: every list is a permutation of itself (`List.Perm.refl`)
- **Inverse**: if `l₁ ~ l₂` then `l₂ ~ l₁` (`List.Perm.symm`)
- **Composition**: if `l₁ ~ l₂` and `l₂ ~ l₃` then `l₁ ~ l₃` (`.trans`)

These are exactly the axioms of a *group*. Permutations form one of
the most important groups in mathematics — you'll meet this structure
again in the algebraic_structures course.

**Reusable recipe**: `have h₁ := ..swap..` then `have h₂ := ..swap..`
then `exact h₁.trans h₂`.
"

/-- `List.Perm.trans h₁ h₂` chains two permutations.
From `h₁ : l₁.Perm l₂` and `h₂ : l₂.Perm l₃`, produces `l₁.Perm l₃`.

## Syntax
```
exact h₁.trans h₂
```

## When to use it
When you need to chain multiple rearrangements.
-/
TheoremDoc List.Perm.trans as "List.Perm.trans" in "List"

/-- `List.Perm.length_eq` states that permutations preserve length:
`l₁.Perm l₂ → l₁.length = l₂.length`.

## Syntax
```
have h := hp.length_eq  -- where hp : l₁.Perm l₂
exact hp.length_eq
```

## When to use it
When you have a permutation and need to conclude equal lengths.
-/
TheoremDoc List.Perm.length_eq as "List.Perm.length_eq" in "List"

TheoremTab "List"
NewTheorem List.Perm.trans List.Perm.length_eq

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
