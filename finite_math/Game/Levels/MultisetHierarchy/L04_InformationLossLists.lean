import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 4

Title "Information loss: same bag, different lists"

Introduction
"
# Experiencing information loss

You just proved that `[1, 2, 3]` and `[3, 1, 2]` give the same multiset.
But are those lists actually **different**? Of course they are -- `[1, 2, 3]`
starts with `1`, while `[3, 1, 2]` starts with `3`. But this difference
is invisible at the multiset level.

Information loss is only visceral when you demonstrate both sides:
- the two things are **distinguishable** at the lower level (they are different lists)
- they become **indistinguishable** at the higher level (they are the same multiset)

## Your task

Prove the conjunction:
1. The lists `[1, 2, 3]` and `[3, 1, 2]` are **different** as lists
2. The lists `[1, 2, 3]` and `[3, 1, 2]` produce the **same** multiset

This makes the information loss concrete: coercion to a multiset erases
the difference between these two lists.

**Strategy**:
1. Use `constructor` to split the conjunction
2. For the inequality, use `decide`
3. For the multiset equality, use `rw [Multiset.coe_eq_coe]` then `decide`
"

/-- Two different lists can produce the same multiset. -/
Statement : [1, 2, 3] ≠ ([3, 1, 2] : List Nat) ∧
    (↑([1, 2, 3] : List Nat) : Multiset Nat) = ↑([3, 1, 2] : List Nat) := by
  Hint "The goal is a conjunction: a list inequality **and** a multiset equality.
  Split it with `constructor`."
  constructor
  · Hint "The goal is `[1, 2, 3] ≠ [3, 1, 2]`. This is a concrete inequality
    between two specific lists. What tactic can decide concrete propositions?"
    Hint (hidden := true) "Try `decide`. It can evaluate the inequality on concrete lists."
    decide
  · Hint "Now prove that the two lists give the same multiset. You did this in
    the previous level. What bridge lemma converts multiset equality to a
    permutation check?"
    Hint (hidden := true) "Use `rw [Multiset.coe_eq_coe]` to reduce to a permutation,
    then `decide`."
    rw [Multiset.coe_eq_coe]
    decide

Conclusion
"
You have now **experienced** information loss, not just been told about it.

The two lists `[1, 2, 3]` and `[3, 1, 2]` are genuinely different: they have
different first elements, different orderings. Yet when you coerce them to
multisets with `↑`, the difference vanishes. The multiset `↑[1, 2, 3]`
and the multiset `↑[3, 1, 2]` are the **same object**.

This is what it means for the coercion `↑ : List α → Multiset α` to
\"forget order\": it is a many-to-one function. Multiple distinct inputs
(different orderings of the same elements) map to a single output.

**In plain language**: \"Two different sequences can fill the same bag.
Once the items are in the bag, you cannot tell which sequence put them there.\"
"

DisabledTactic trivial native_decide simp aesop simp_all
