import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 8

Title "Cardinality by peeling"

Introduction
"
# Computing cardinality structurally

You know that `Finset.card_singleton` gives `({a}).card = 1`. But how
do you compute the cardinality of `{1, 2, 3}` -- a finset built by
multiple `insert` calls?

## `Finset.card_insert_of_notMem`

The key lemma is:

```
Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1
```

If `a` is not already in `s`, inserting it increases the cardinality by 1.

## The peeling pattern

To compute `{1, 2}.card`:
1. Recall that `{1, 2}` means `insert 1 {2}`.
2. Since `1 ∉ {2}`, apply `card_insert_of_notMem` to get `{2}.card + 1`.
3. Apply `card_singleton` to get `1 + 1 = 2`.

## Your task

Prove that `(insert 1 {2, 3}).card = 3`. You are given the hypothesis
`h : (1 : Nat) ∉ ({2, 3} : Finset Nat)` (which you can trust without
proving). Use `card_insert_of_notMem h` to peel off the outer insert,
then the inner finset `{2, 3}` has cardinality 2 by `decide`.
"

/-- The cardinality of `insert 1 {2, 3}` is 3. -/
Statement (h : (1 : Nat) ∉ ({2, 3} : Finset Nat)) :
    (insert 1 ({2, 3} : Finset Nat)).card = 3 := by
  Hint "The goal is `(insert 1 s).card = 3` where `s = Finset with elements 2 and 3`.
  You have `h : 1 ∉ s`. What lemma lets you peel off the `insert` and
  relate the cardinality to `s.card + 1`?"
  Hint (hidden := true) "Use `rw [Finset.card_insert_of_notMem h]`. This reduces
  the goal to `s.card + 1 = 3`, where `s.card = 2`."
  rw [Finset.card_insert_of_notMem h]
  Hint "The goal is now a cardinality equation for a literal finset.
  The remaining computation is concrete."
  Hint (hidden := true) "Try `decide`."
  decide

Conclusion
"
You used `card_insert_of_notMem` to peel off the outer `insert`, reducing
the cardinality of the larger finset to the cardinality of the smaller one
plus 1.

This **peeling pattern** is how cardinality of literal finsets works in Lean:
- `card_insert_of_notMem h` strips one `insert` layer: `(insert a s).card = s.card + 1`
- `card_singleton` handles the base case: `({a}).card = 1`
- `card_empty` handles the empty case: `∅.card = 0`

Together, these three lemmas let you compute the cardinality of any finset
built by iterated `insert`, step by step.

**In plain language**: \"To count the elements of a set built by successive
additions, check that each new element is genuinely new (not a duplicate),
then add 1 for each.\"
"

/-- `Finset.card_insert_of_notMem` states that if `a ∉ s`, then
`(insert a s).card = s.card + 1`.

Inserting a genuinely new element increases the cardinality by 1.
Combined with `Finset.card_singleton` and `Finset.card_empty`, this
lets you compute the cardinality of any literal finset step by step. -/
TheoremDoc Finset.card_insert_of_notMem as "Finset.card_insert_of_notMem" in "Finset"

NewTheorem Finset.card_insert_of_notMem
DisabledTactic trivial native_decide simp aesop simp_all
