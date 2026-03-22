import Game.Metadata

World "AbstractionLadder"
Level 6

Title "Permutations"

Introduction "
# Lists Are Ordered — Permutations Ignore Order

Two lists with the same elements in different orders are **not** equal:
`[1, 2, 3] ≠ [2, 1, 3]`. Order is part of a list's identity.

But sometimes we want to say 'these lists have the same elements,
just rearranged.' That's `List.Perm` — the permutation relation.

We write `l₁ ~ l₂` (or `l₁.Perm l₂`) to mean `l₁` is a permutation
of `l₂`.

The key building blocks:

- **`List.Perm.swap x y l`** — swapping two adjacent elements gives
  a permutation: `[y, x] ++ l ~ [x, y] ++ l`
- **`List.Perm.cons a h`** — if `l₁ ~ l₂`, then `a :: l₁ ~ a :: l₂`
  (prepending the same element preserves the permutation)
- **`List.Perm.trans h₁ h₂`** — if `l₁ ~ l₂` and `l₂ ~ l₃`,
  then `l₁ ~ l₃` (chain permutations)

**Your task**: Prove that `[2, 1, 3]` is a permutation of `[1, 2, 3]`.
This is a single swap of the first two elements.
"

/-- Swapping the first two elements gives a permutation. -/
Statement : List.Perm [2, 1, 3] [1, 2, 3] := by
  Hint "The lists `[2, 1, 3]` and `[1, 2, 3]` differ only in the order
  of the first two elements. This is exactly `List.Perm.swap 1 2 [3]`."
  Hint (hidden := true) "Try `exact List.Perm.swap 1 2 [3]`.
  This says: swapping `1` and `2` in front of `[3]` gives
  `[2, 1, 3] ~ [1, 2, 3]`."
  exact List.Perm.swap 1 2 [3]

Conclusion "
`List.Perm.swap` is the atomic permutation move: swap two adjacent
elements. Every permutation can be built from a sequence of swaps.

The type signature: `List.Perm.swap x y l : (y :: x :: l).Perm (x :: y :: l)`.

Note the argument order: `swap x y l` produces `[y, x, ...] ~ [x, y, ...]`.
The elements appear **reversed** on the left side.

**Why permutations matter for the ladder**: The `Multiset` type is
defined as the quotient `List α / Perm`. Two lists that are
permutations of each other become the **same** multiset. This is
how order gets forgotten.
"

/-- `List.Perm` is the permutation relation on lists. `l₁.Perm l₂`
(notation: `l₁ ~ l₂`) means `l₁` is a rearrangement of `l₂`.

## Building permutations
- `List.Perm.swap x y l : (y :: x :: l).Perm (x :: y :: l)` — swap adjacent
- `List.Perm.cons a h : (a :: l₁).Perm (a :: l₂)` from `h : l₁.Perm l₂`
- `List.Perm.trans h₁ h₂` — chain two permutations

## Key facts
- `List.Perm.length_eq : l₁.Perm l₂ → l₁.length = l₂.length`
- `Multiset.coe_eq_coe : ↑l₁ = ↑l₂ ↔ l₁.Perm l₂`
-/
DefinitionDoc List.Perm as "List.Perm"

/-- `List.Perm.swap x y l` proves `(y :: x :: l).Perm (x :: y :: l)`.

## Syntax
```
exact List.Perm.swap x y l
```

## When to use it
When two lists differ only by a swap of two adjacent elements.

## Warning
The arguments `x y` appear in the *reverse* order on the left:
`swap x y l` gives `[y, x, ...] ~ [x, y, ...]`.
-/
TheoremDoc List.Perm.swap as "List.Perm.swap" in "List"

/-- `List.Perm.cons a h` proves `(a :: l₁).Perm (a :: l₂)` from
`h : l₁.Perm l₂`.

## Syntax
```
exact List.Perm.cons a h
```

## When to use it
When two lists have the same head and their tails are permutations.
-/
TheoremDoc List.Perm.cons as "List.Perm.cons" in "List"

TheoremTab "List"
NewDefinition List.Perm
NewTheorem List.Perm.swap List.Perm.cons

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
