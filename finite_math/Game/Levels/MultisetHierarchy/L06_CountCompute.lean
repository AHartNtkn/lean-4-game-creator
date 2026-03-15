import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 6

Title "Counting occurrences"

Introduction
"
# Multisets keep duplicates

A crucial difference between multisets and finsets:

- A **multiset** can contain repeated elements. The multiset `↑[1, 2, 1, 3]`
  has **four** elements: two copies of `1`, one copy of `2`, and one copy of `3`.
- A **finset** (which you will see later) contains each element **at most once**.

## `Multiset.count`

The function `Multiset.count a m` counts how many times element `a` appears
in multiset `m`. For example:
- `Multiset.count 1 (↑[1, 2, 1, 3]) = 2`
- `Multiset.count 2 (↑[1, 2, 1, 3]) = 1`
- `Multiset.count 5 (↑[1, 2, 1, 3]) = 0`

This is one of the things that distinguishes multisets from finsets: a
multiset tracks the **multiplicity** of each element.

## Your task

Prove that the element `1` appears exactly twice in the multiset obtained
from `[1, 2, 1, 3]`.

For this concrete computation, `decide` will work.
"

/-- The element `1` appears twice in the multiset `↑[1, 2, 1, 3]`. -/
Statement : Multiset.count 1 (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) = 2 := by
  Hint "The goal is a concrete equality about counting in a specific multiset.
  Both sides can be evaluated to natural numbers. What tactic evaluates concrete
  decidable propositions?"
  Hint (hidden := true) "Try `decide`. It can evaluate `Multiset.count` on a
  concrete multiset and verify the result."
  decide

Conclusion
"
The multiset `↑[1, 2, 1, 3]` contains four elements, and the element `1`
appears twice. This is the key property that distinguishes multisets from
finsets:

| Collection | Remembers order? | Remembers multiplicity? |
|-----------|-----------------|------------------------|
| `List`    | Yes             | Yes                    |
| `Multiset`| **No**          | Yes                    |
| `Finset`  | **No**          | **No**                 |

A multiset forgets the order of a list, but **keeps track of how many
times each element appears**. Later, when you convert a multiset to a
finset, the multiplicity information will be lost too.

In the next level, you will learn to reason about `Multiset.count` **symbolically**
-- not just by computing on concrete examples, but by using rewriting lemmas
that describe the recursive structure of counting.

**In plain language**: \"In a bag of marbles, it matters how many red
marbles you have, even though the order you put them in does not matter.\"
"

/-- `Multiset.count a m` returns the number of times element `a` appears in
multiset `m`. For example, `Multiset.count 1 ↑[1, 2, 1, 3] = 2`.

Unlike finset membership (which is boolean: in or not in), multiset count
gives a natural number -- the **multiplicity** of the element. -/
DefinitionDoc Multiset.count as "Multiset.count"

NewDefinition Multiset.count
DisabledTactic trivial native_decide simp aesop simp_all
