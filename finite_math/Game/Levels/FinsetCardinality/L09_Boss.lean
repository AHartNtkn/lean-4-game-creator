import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 9

Title "Boss: Cardinality computation"

Introduction
"
# Boss: Putting cardinality tools together

Time to integrate everything from this world. You will prove three
cardinality facts using the lemmas you have learned.

## What you need

1. **Part 1**: Use `card_range` to compute a range cardinality.
2. **Part 2**: Use inclusion-exclusion (`card_union_add_card_inter`)
   to relate union, intersection, and individual cardinalities.
3. **Part 3**: Use `card_filter_le` to bound the cardinality of a
   filtered finset.

Each part uses a single lemma from this world. The challenge is
selecting the right tool for each goal.
"

/-- Three cardinality facts demonstrating range, inclusion-exclusion, and filter. -/
Statement : (Finset.range 10).card = 10 ∧
    (({1, 2, 3} : Finset Nat) ∪ {3, 4, 5}).card +
      (({1, 2, 3} : Finset Nat) ∩ {3, 4, 5}).card =
      ({1, 2, 3} : Finset Nat).card + ({3, 4, 5} : Finset Nat).card ∧
    (Finset.filter (fun x => x < 3)
      ({1, 2, 3, 4, 5} : Finset Nat)).card ≤
      ({1, 2, 3, 4, 5} : Finset Nat).card := by
  Hint "The goal is a three-part conjunction. Split it with `refine ⟨?_, ?_, ?_⟩`
  or use `constructor` twice."
  Hint (hidden := true) "Use `refine ⟨?_, ?_, ?_⟩`."
  refine ⟨?_, ?_, ?_⟩
  · Hint "**Part 1**: Prove `(Finset.range 10).card = 10`. Which lemma
    gives the cardinality of `range n`?"
    Hint (hidden := true) "Use `rw [Finset.card_range]` or
    `exact Finset.card_range 10`."
    exact Finset.card_range 10
  · Hint "**Part 2**: This is an instance of the inclusion-exclusion
    principle. Which lemma states
    `(s ∪ t).card + (s ∩ t).card = s.card + t.card`?"
    Hint (hidden := true) "Use `exact Finset.card_union_add_card_inter _ _`."
    exact Finset.card_union_add_card_inter _ _
  · Hint "**Part 3**: This asks for a cardinality inequality after
    filtering. Which lemma bounds the cardinality of `s.filter p`?"
    Hint (hidden := true) "Use `exact Finset.card_filter_le _ _`."
    exact Finset.card_filter_le _ _

Conclusion
"
Congratulations on completing the Cardinality world!

You proved three facts, each requiring a different cardinality tool:

1. **Range cardinality** (L05): `card_range` gives `(range n).card = n`.
2. **Inclusion-exclusion** (L07): `card_union_add_card_inter` relates
   the cardinalities of unions and intersections.
3. **Filter bound** (L08): `card_filter_le` says filtering cannot
   increase cardinality.

## What you learned in this world

| Concept | Level | Key lemma |
|---------|-------|-----------|
| Base case | L01 | `card_empty` |
| Singleton | L02 | `card_singleton` (retrieval) |
| Insert new | L03 | `card_insert_of_notMem` (retrieval) |
| Insert duplicate | L04 | `card_insert_of_mem` |
| Range cardinality | L05 | `card_range` |
| Range boundary | L06 | `range_zero` |
| Inclusion-exclusion | L07 | `card_union_add_card_inter` |
| Filter bound | L08 | `card_filter_le` |
| Integration | L09 | All of the above |

## Transfer moment

The cardinality toolkit in Lean mirrors the counting toolkit in
ordinary mathematics:

- **Insertion counting**: Adding a new element increases the count by 1;
  adding a duplicate does not.
- **Range counting**: The set {0, 1, ..., n-1} has n elements.
- **Inclusion-exclusion**: |A ∪ B| = |A| + |B| - |A ∩ B|.
- **Filter bound**: Selecting elements from a set cannot produce
  more elements.

The Lean versions are more precise (they require non-membership proofs,
use the additive form of inclusion-exclusion, etc.), but the underlying
ideas are identical.

## What comes next

The next world introduces **Finset induction**: proving properties of
all finsets by building them up from `∅` one `insert` at a time. This
is the structural induction principle for finsets, and it will let you
prove general cardinality results rather than just compute specific ones.
"

DisabledTactic trivial decide native_decide aesop simp_all
