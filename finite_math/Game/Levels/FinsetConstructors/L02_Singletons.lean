import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 2

Title "Singletons and cardinality"

Introduction
"
# Building a finset with one element

The next step up from the empty finset is a finset with exactly one element:
a **singleton**. When you write `{5}` in a finset context, Lean builds a
finset containing only the element `5`.

## How singletons are built

Under the hood, `{5}` is the same as `insert 5 ∅` -- start with the empty
finset and insert one element. (You will learn about `insert` in the
next level.)

## Cardinality

The **cardinality** of a finset is the number of elements it contains.
In Lean, `Finset.card s` (or `s.card`) gives this count.

## Your task

Prove that the singleton finset `{5}` has cardinality 1. The key lemma is
`Finset.card_singleton`, which states:

```
Finset.card_singleton a : ({a} : Finset α).card = 1
```

After rewriting with this lemma, the goal is closed.
"

/-- The singleton finset `{5}` has exactly 1 element. -/
Statement : ({5} : Finset Nat).card = 1 := by
  Hint "The goal asks for the cardinality of a concrete singleton finset.
  You need a lemma about the cardinality of singletons. The lemma
  `Finset.card_singleton` states that the cardinality of any singleton
  finset is 1."
  Hint (hidden := true) "Use `rw [Finset.card_singleton]` to rewrite the
  left-hand side to `1`, then the goal closes automatically."
  rw [Finset.card_singleton]

Conclusion
"
The singleton finset `{a}` contains exactly one element, so its cardinality
is always 1. This is the simplest nonempty finset.

Notice the pattern so far:
- `∅` has cardinality 0 (the lemma `Finset.card_empty` says `(∅ : Finset α).card = 0`)
- `{a}` has cardinality 1 (the lemma `Finset.card_singleton` says `({a}).card = 1`)

In the next level, you will see how `{a, b}` is built from these primitives
using `insert`.

**A subtle point**: `{5}` as a `Finset Nat` and `{5}` as a `Set Nat` are
*different types* in Lean, even though they look the same on paper. The
Lean elaborator determines which one you mean from context. We will
explore this distinction later in the world.

**In plain language**: \"The set containing just the number 5 has exactly
one element.\"
"

/-- `Finset.card_singleton a` states that `({a} : Finset α).card = 1`.
A singleton finset has exactly one element. -/
TheoremDoc Finset.card_singleton as "Finset.card_singleton" in "Finset"

NewTheorem Finset.card_singleton
DisabledTactic trivial decide native_decide simp aesop simp_all
