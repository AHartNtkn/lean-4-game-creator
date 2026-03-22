import Game.Metadata

World "BigOpIntro"
Level 3

Title "Peeling Off One Element"

Introduction "
# sum_insert: The Recursive Step

You know that `{1, 2}` in Lean is sugar for `insert 1 {2}`. The key
lemma for computing sums over such finsets peels off the inserted
element:

$$a \\notin s \\implies \\sum_{x \\in \\{a\\} \\cup s} f(x) = f(a) + \\sum_{x \\in s} f(x)$$

In Lean:
```
Finset.sum_insert : a ∉ s → ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x
```

The hypothesis `a ∉ s` is required because `insert` into a finset is
idempotent — if `a` is already in `s`, then `insert a s = s` and the
equation would be wrong (it would double-count `a`).

For this level, we've provided the non-membership proof as a hypothesis
`h`. In later levels, you'll prove it yourself.

**Your task**: Prove that `∑ x ∈ insert 5 s, f x = f 5 + ∑ x ∈ s, f x`.
"

/-- Peeling one element off a sum using sum_insert. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (h : (5 : ℕ) ∉ s) :
    ∑ x ∈ insert 5 s, f x = f 5 + ∑ x ∈ s, f x := by
  Hint "The goal matches the shape of `Finset.sum_insert`. You have the
  hypothesis `h : 5 ∉ s` ready to use.
  Try `rw [Finset.sum_insert h]`."
  Hint (hidden := true) "Use `rw [Finset.sum_insert h]` to peel off the
  inserted element."
  rw [Finset.sum_insert h]

Conclusion "
`Finset.sum_insert` is the workhorse of concrete sum computation.
It peels off one element at a time:

$$\\sum_{x \\in \\{a\\} \\cup s} f(x) = f(a) + \\sum_{x \\in s} f(x)$$

Combined with `sum_singleton` (to handle the final one-element set)
and `sum_empty` (to handle the truly empty case), you can now unfold
any sum over a finite literal set into individual terms.

The pattern: repeated `sum_insert` peels elements until you reach a
singleton, then `sum_singleton` finishes.

**Important**: `sum_insert` requires a proof that the element being
peeled off is NOT already in the remaining set. In the next level,
you'll prove this non-membership yourself.

**Connection**: Notice the similarity to `card_insert_of_notMem`
from the Cardinality world: $|\\{a\\} \\cup s| = 1 + |s|$. That's
the special case of `sum_insert` with `f = fun \\_ => 1` — cardinality
is summation where every element contributes 1. You'll see this
made precise in a later level.
"

/-- `Finset.sum_insert` states that if `a ∉ s`, then
`∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x`.

## Syntax
```
rw [Finset.sum_insert h]  -- where h : a ∉ s
```

## When to use it
When the goal involves a sum over `insert a s` (which includes
`{a, b, ...}` since this is sugar for nested inserts). You need
a proof `h : a ∉ s` to apply it.

## Example
```
-- h : 1 ∉ {2, 3}
-- Goal: ∑ x ∈ {1, 2, 3}, f x = ...
rw [Finset.sum_insert h]
-- Goal: f 1 + ∑ x ∈ {2, 3}, f x = ...
```

## Warning
Without the `a ∉ s` proof, `sum_insert` cannot fire. You must
prove non-membership first (usually with `rw [Finset.mem_singleton]`
or `rw [Finset.mem_insert, Finset.mem_singleton]` followed by `omega`).
-/
TheoremDoc Finset.sum_insert as "Finset.sum_insert" in "BigOp"

NewTheorem Finset.sum_insert

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.sum_pair Finset.prod_pair
