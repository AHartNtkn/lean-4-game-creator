import Game.Metadata

World "BigOpIntro"
Level 1

Title "The Empty Sum"

Introduction "
# Big Operators: ∑ and ∏

Welcome to **big operators** — Lean's way of writing sums and products
over finsets.

The notation `∑ x ∈ s, f x` means: *sum f(x) over all elements x in
the finset s*. In ordinary math notation:

$$\\sum_{x \\in s} f(x)$$

This is `Finset.sum s f` in Lean. It requires an `AddCommMonoid` —
a type with `+` and `0` where addition is commutative and associative.
For natural numbers, this is automatic.

The most fundamental fact: **the sum over the empty set is zero**.

$$\\sum_{x \\in \\emptyset} f(x) = 0$$

This is `Finset.sum_empty`:
```
Finset.sum_empty : ∑ x ∈ ∅, f x = 0
```

This is the additive identity — the base case for building up sums.
Just as `∅` was the starting point for building finsets, the empty sum
is the starting point for big-operator reasoning.

**Your task**: You know that `s` is empty. Prove that the sum of `f`
over `s` is zero.
"

/-- The sum of any function over the empty finset is zero. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hs : s = ∅) :
    ∑ x ∈ s, f x = 0 := by
  Hint "The hypothesis `hs` tells you `s = ∅`. First substitute
  with `rw [hs]`, then the goal becomes a sum over `∅`."
  rw [hs]
  Hint "Now the goal is `∑ x ∈ ∅, f x = 0`. This is exactly what
  `Finset.sum_empty` says. Close with `exact Finset.sum_empty`.

  (If you tried `rfl` and it didn't work: `rfl` is disabled in this
  world to help you learn the explicit lemma names for each big-operator
  identity. These names will be essential when the goals aren't simple
  equalities.)"
  Hint (hidden := true) "Try `exact Finset.sum_empty`."
  exact Finset.sum_empty

Conclusion "
`Finset.sum_empty` is the base case for sums: the empty sum equals
the additive identity (zero for ℕ, and more generally for any
`AddCommMonoid`).

In plain math: $\\sum_{{x \\in \\emptyset}} f(x) = 0$.

This parallels `Finset.card_empty`: just as $|\\emptyset| = 0$,
the empty sum is zero regardless of the function.
"

/-- `Finset.sum_empty` states that `∑ x ∈ ∅, f x = 0`.

## Syntax
```
exact Finset.sum_empty
rw [Finset.sum_empty]
```

## When to use it
When the goal or a hypothesis involves a sum over the empty finset.
The empty sum always equals `0` (the additive identity).

## Warning
The empty sum is `0`, not undefined. This is a convention that
makes inductive arguments work — just as $0! = 1$ by convention.
-/
TheoremDoc Finset.sum_empty as "Finset.sum_empty" in "BigOp"

/-- `Finset.sum s f` (written `∑ x ∈ s, f x`) computes the sum of
`f x` over all elements `x` in the finset `s`.

## Notation
`∑ x ∈ s, f x` — sum of `f` over finset `s`.

## Type
`Finset.sum : Finset ι → (ι → M) → M` where `M` has `AddCommMonoid`.

## Key lemmas
- `Finset.sum_empty : ∑ x ∈ ∅, f x = 0`
- `Finset.sum_singleton : ∑ x ∈ {a}, f x = f a`
- `Finset.sum_insert : a ∉ s → ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x`
-/
DefinitionDoc Finset.sum as "Finset.sum"

TheoremTab "BigOp"
NewDefinition Finset.sum
NewTheorem Finset.sum_empty

-- Note: rfl is disabled in BigOpIntro to force learning explicit lemma names
-- (sum_empty, sum_singleton, sum_insert, etc.) rather than bypassing them.
DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
