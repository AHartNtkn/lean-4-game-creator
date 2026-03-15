import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 6

Title "insert absorbs duplicates"

Introduction
"
# Inserting a duplicate does nothing

In ordinary mathematics, adding an element to a set that already contains
it leaves the set unchanged: $\\{1, 2, 3\\} \\cup \\{2\\} = \\{1, 2, 3\\}$.
The same is true for `Finset.insert` in Lean.

## `Finset.insert_eq_of_mem`

The key lemma is:

```
Finset.insert_eq_of_mem : a ∈ s → insert a s = s
```

If `a` is already in `s`, then inserting it again produces the same finset.
This is what makes finsets behave like mathematical sets rather than lists:
**no duplicates**.

## Why this matters

This is not just a technicality. It has consequences for reasoning:

- `insert 2 {1, 2, 3} = {1, 2, 3}` -- redundant inserts are harmless.
- The cardinality does not change: if `a ∈ s`, then
  `(insert a s).card = s.card`.
- When you build a finset by iterated `insert`, order and repetition
  do not matter -- only which elements are present.

## Your task

Prove that `insert 2 ({1, 2, 3} : Finset Nat) = {1, 2, 3}`.

**Strategy**: Apply `Finset.insert_eq_of_mem`. This reduces the goal to
showing `2 ∈ {1, 2, 3}`, which you already know how to prove.
"

/-- Inserting `2` into `{1, 2, 3}` does not change the finset. -/
Statement : insert 2 ({1, 2, 3} : Finset Nat) = {1, 2, 3} := by
  Hint "To prove that inserting a duplicate leaves the finset unchanged,
  use `Finset.insert_eq_of_mem`. This transforms the equality goal
  into a membership goal: you must show that `2` is already in the
  finset."
  Hint (hidden := true) "Use `apply Finset.insert_eq_of_mem`."
  apply Finset.insert_eq_of_mem
  Hint "The goal is now a membership question: `2 ∈` the finset containing
  1, 2, 3. You have proved goals like this before. You can use `simp`
  with the membership lemmas, or rewrite manually."
  Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
  simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
You just saw that `insert` on finsets **absorbs duplicates**: inserting an
element that is already present has no effect. This is a fundamental
property that distinguishes finsets from lists. (In mathematical terms,
this is the *absorption law*: `s ∪ {a} = s` when `a ∈ s`.)

Compare with lists:
- `List`: `[1, 2, 3] ++ [2] = [1, 2, 3, 2]` -- duplicates accumulate.
- `Finset`: `insert 2 {1, 2, 3} = {1, 2, 3}` -- duplicates are absorbed.

## The proof pattern

The proof combined two ideas:
1. **`insert_eq_of_mem`** reduced the equality to a membership question.
2. **`simp`** with membership lemmas answered the membership question.

This two-step pattern (reduce to membership, then solve membership) will
recur whenever you need to simplify finsets with redundant inserts.

**In plain language**: \"Adding 2 to {1, 2, 3} does nothing because 2 is
already there. Sets do not have duplicates.\"
"

/-- `Finset.insert_eq_of_mem` states that if `a ∈ s`, then
`insert a s = s`.

Inserting a duplicate element has no effect on a finset.
This is the absorption property: duplicates are silently dropped. -/
TheoremDoc Finset.insert_eq_of_mem as "Finset.insert_eq_of_mem" in "Finset"

NewTheorem Finset.insert_eq_of_mem
DisabledTactic trivial decide native_decide aesop simp_all
