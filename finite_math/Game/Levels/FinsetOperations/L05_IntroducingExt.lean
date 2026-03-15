import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 5

Title "Introducing ext"

Introduction
"
# Proving finset equality with `ext`

So far you have proved **membership** facts: showing that a specific
element belongs to a specific finset expression. But what about proving
that two finsets are **equal**?

## The extensionality principle

Two finsets are equal if and only if they have the same elements:

```
Finset.ext_iff : s = t ↔ ∀ a, a ∈ s ↔ a ∈ t
```

This is the **extensionality** principle: the identity of a finset is
determined entirely by its members.

## The `ext` tactic

The tactic `ext a` converts a goal `s = t` into `∀ a, a ∈ s ↔ a ∈ t`,
then introduces `a` for you. After `ext a`, you need to prove a
biconditional `a ∈ s ↔ a ∈ t`.

To prove a biconditional `P ↔ Q`, use `constructor` to split into two
implications `P → Q` and `Q → P`, then prove each separately.

## Your task

Prove that `s ∪ t = t ∪ s` for arbitrary finsets `s` and `t`. This is
the **commutativity of union**.

**Strategy**: Use `ext a` to reduce to membership, then `constructor`
to split the biconditional. In each direction, rewrite with
`Finset.mem_union` and use `rcases` to swap the disjuncts.
"

/-- Union of finsets is commutative. -/
Statement (s t : Finset Nat) : s ∪ t = t ∪ s := by
  Hint "The goal is a finset equality: `s ∪ t = t ∪ s`. To prove two
  finsets are equal, show they have the same elements. Use the `ext`
  tactic to introduce an arbitrary element `a` and reduce to a
  membership biconditional."
  Hint (hidden := true) "Use `ext a`."
  ext a
  Hint "The goal is now `a ∈ s ∪ t ↔ a ∈ t ∪ s`. This is a biconditional.
  Split it into two implications using `constructor`."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · Hint "Prove the forward direction: `a ∈ s ∪ t → a ∈ t ∪ s`.
    Introduce the hypothesis."
    Hint (hidden := true) "Use `intro h`."
    intro h
    Hint "Now `h : a ∈ s ∪ t`. Rewrite `h` with `mem_union` to get
    a disjunction, then case-split."
    Hint (hidden := true) "Use `rw [Finset.mem_union] at h`, then
    `rcases h with hs | ht`."
    rw [Finset.mem_union] at h
    rcases h with hs | ht
    · Hint "In this case `hs : a ∈ s`. You need `a ∈ t ∪ s`. Rewrite
      the goal with `mem_union` and choose the right branch."
      Hint (hidden := true) "Use `rw [Finset.mem_union]`, then `right`,
      then `exact hs`."
      rw [Finset.mem_union]
      right
      exact hs
    · Hint "In this case `ht : a ∈ t`. You need `a ∈ t ∪ s`. Rewrite
      the goal and choose the left branch."
      Hint (hidden := true) "Use `rw [Finset.mem_union]`, then `left`,
      then `exact ht`."
      rw [Finset.mem_union]
      left
      exact ht
  · Hint "Now prove the reverse direction: `a ∈ t ∪ s → a ∈ s ∪ t`.
    The argument is symmetric."
    Hint (hidden := true) "Use `intro h`."
    intro h
    Hint "Rewrite and case-split, then swap the branches."
    Hint (hidden := true) "Use `rw [Finset.mem_union] at h`,
    `rcases h with ht | hs`, then in each case `rw [Finset.mem_union]`
    and choose the appropriate branch."
    rw [Finset.mem_union] at h
    rcases h with ht | hs
    · rw [Finset.mem_union]
      right
      exact ht
    · rw [Finset.mem_union]
      left
      exact hs

Conclusion
"
You just proved **commutativity of union** using the `ext` tactic.
This is a fundamental proof pattern for finset equality:

1. **`ext a`** -- reduce \"same finset\" to \"same elements\".
2. **`constructor`** -- split the biconditional into two implications.
3. In each direction, **rewrite** membership with the operation's
   lemma and **rearrange** the logical pieces.

## The `ext` proof shape

The `ext` proof shape corresponds exactly to the standard mathematical
proof of a set equality:

> \"To show S = T, take an arbitrary element a. We show a ∈ S ↔ a ∈ T.\"

This is **extensionality**: two collections are equal iff they have the
same members. Every set-equality proof in ordinary mathematics has
this shape, and `ext` is the Lean tactic that initiates it.

**In plain language**: \"s ∪ t = t ∪ s because for any element a, being
in s or t is the same as being in t or s.\"
"

/-- The `ext` tactic proves an equality between two structures by showing they
agree on all components. For finsets, `ext a` converts the goal `s = t` into
`∀ a, a ∈ s ↔ a ∈ t`.

After `ext a`, you need to prove a biconditional about membership, which you
can split with `constructor` and handle each direction separately.

This corresponds to the mathematical proof pattern: \"To show two sets are
equal, show they have the same elements.\" -/
TacticDoc ext

NewTactic ext
DisabledTactic trivial decide native_decide aesop simp_all
