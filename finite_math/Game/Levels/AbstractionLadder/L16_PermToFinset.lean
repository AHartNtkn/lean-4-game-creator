import Game.Metadata

World "AbstractionLadder"
Level 16

Title "Permutations Give Equal Finsets"

Introduction "
# Permuted Lists → Same Finset

If two lists are permutations of each other, they contain the same
elements. So their `toFinset` values must be equal:

`List.toFinset_eq_of_perm l₁ l₂ h : l₁.toFinset = l₂.toFinset`
  (from `h : l₁.Perm l₂`)

This is the key link between the List and Finset layers: permutations
are invisible to `toFinset`.

**Your task**: Prove that `[2, 3, 1]` and `[1, 2, 3]` give the same
finset. You'll need to build the permutation proof first, then apply
`List.toFinset_eq_of_perm`.

Notice this uses **different** concrete lists from the multiset level
(L09). The same technique applies, but you need to find new swaps.
"

/-- Permuted lists give equal finsets. -/
Statement : ([2, 3, 1] : List ℕ).toFinset = [1, 2, 3].toFinset := by
  Hint "You need a permutation proof to apply `List.toFinset_eq_of_perm`.
  Use `apply List.toFinset_eq_of_perm` to reduce the finset equality
  to a permutation goal."
  apply List.toFinset_eq_of_perm
  Hint "Now prove `[2, 3, 1] ~ [1, 2, 3]`. Find an intermediate list
  and chain two swaps."
  Hint (hidden := true) "Chain two swaps via `[2, 1, 3]`:
  `have h1 : List.Perm [2, 3, 1] [2, 1, 3] := List.Perm.cons 2 (List.Perm.swap 1 3 [])`
  `have h2 : List.Perm [2, 1, 3] [1, 2, 3] := List.Perm.swap 1 2 [3]`
  `exact h1.trans h2`"
  have h1 : List.Perm [2, 3, 1] [2, 1, 3] := List.Perm.cons 2 (List.Perm.swap 1 3 [])
  have h2 : List.Perm [2, 1, 3] [1, 2, 3] := List.Perm.swap 1 2 [3]
  exact h1.trans h2

Conclusion "
Permutations are invisible to `toFinset` — rearranging a list doesn't
change which elements it contains, so the resulting finset is the same.

This is another way to see why `Multiset` is the intermediate layer:
- `List → Multiset` quotients by permutation (forgets order)
- `Multiset → Finset` deduplicates (forgets multiplicities)
- `List → Finset` does both at once via `toFinset`

Since `toFinset` already forgets order, two lists that differ only in
order (i.e., are permutations) naturally map to the same finset.

**Reusable recipe**: When you have a perm and need equal finsets,
apply `List.toFinset_eq_of_perm`.
"

/-- `List.toFinset_eq_of_perm l₁ l₂ h` proves
`l₁.toFinset = l₂.toFinset` from `h : l₁.Perm l₂`.

## Syntax
```
exact List.toFinset_eq_of_perm l₁ l₂ h
apply List.toFinset_eq_of_perm
```

## When to use it
When you have a permutation proof and need to conclude
the two lists give the same finset.
-/
TheoremDoc List.toFinset_eq_of_perm as "List.toFinset_eq_of_perm" in "List"

TheoremTab "List"
NewTheorem List.toFinset_eq_of_perm

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
