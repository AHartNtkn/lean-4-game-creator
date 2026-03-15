import GameServer.Commands
import Mathlib

World "ListUnderLenses"
Level 5

Title "Mapping preserves cardinality"

Introduction
"
# Transforming the data

So far, you have looked at `[1, 2, 1, 3]` through different lenses --
list, multiset, finset -- and compared what each lens preserves.

Now consider a **transformation**: apply a function to every element.
For example, add 10 to each element:

```
[1, 2, 1, 3]  →  [11, 12, 11, 13]
```

As a multiset, this is `Multiset.map (· + 10) ↑[1, 2, 1, 3]`.

## Does mapping change the cardinality?

Intuitively, no. Applying a function to each element does not add or
remove elements -- it replaces each one. So the cardinality should be
unchanged.

The lemma `Multiset.card_map` says exactly this:

```
Multiset.card_map (f : α → β) (m : Multiset α) : (m.map f).card = m.card
```

## Your task

Prove that mapping `(· + 10)` over `↑[1, 2, 1, 3]` does not change the
cardinality.

Use `rw [Multiset.card_map]` to apply the lemma. After the rewrite,
both sides of the equality will be the same, and the goal closes
automatically.

This is the **reduce-then-compute** pattern: the bridge lemma
`Multiset.card_map` does all the work.
"

/-- Mapping a function over a multiset preserves its cardinality. -/
Statement : Multiset.card (Multiset.map (· + 10) (↑([1, 2, 1, 3] : List Nat) : Multiset Nat)) =
    Multiset.card (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) := by
  Hint "The goal says that the cardinality of the mapped multiset equals
  the cardinality of the original. What lemma relates `Multiset.card` and
  `Multiset.map`?"
  Hint (hidden := true) "Use `rw [Multiset.card_map]`. This rewrites
  `(m.map f).card` to `m.card`, making both sides identical."
  rw [Multiset.card_map]

Conclusion
"
The proof was a single rewrite: `rw [Multiset.card_map]` transformed
`(m.map f).card` into `m.card`, and since both sides became identical,
the goal closed automatically (as if `rfl` were applied).

## Why this matters

This is a clean example of **reduce-then-compute** where the \"compute\"
step is trivial (just `rfl`). Compare with Level 2, where the compute step
required `decide`:

| Level | Reduce step | Compute step |
|-------|------------|-------------|
| L02 | `rw [Multiset.mem_coe]` | `decide` |
| L04 | `rw [Multiset.coe_eq_coe]` | `decide` |
| L05 | `rw [Multiset.card_map]` | (automatic / `rfl`) |

The pattern is the same: use a bridge lemma to simplify the goal, then
finish with a concrete computation. Sometimes the computation is trivial
enough that it resolves automatically.

**In plain language**: \"Adding 10 to every item in a bag does not change
how many items are in the bag. The bag `{11, 12, 11, 13}` has the same
count as `{1, 2, 1, 3}`.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all norm_num
