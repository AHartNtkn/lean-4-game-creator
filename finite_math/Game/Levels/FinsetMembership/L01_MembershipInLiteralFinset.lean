import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 1

Title "Membership in a literal finset"

Introduction
"
# Is `1` in `{1, 2, 3}`?

In the previous world you learned to **construct** finsets using `insert`,
`cons`, and the `{a, b, c}` notation. But constructing a finset is only
half the story. The other half is **reasoning about membership**: proving
that a given element is (or is not) in a finset.

## The membership question

When you write `2 ∈ ({1, 2, 3} : Finset Nat)`, you are asking Lean to
verify that `2` appears in the finset built by `insert 1 (insert 2 {3})`.
This is a *proposition* -- something you must prove, not just assert.

## The key lemma: `Finset.mem_insert`

The fundamental membership lemma is:

```
Finset.mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s
```

This says: to check whether `a` is in `insert b s`, either `a` equals
the inserted element `b`, or `a` was already in `s`.

## Your task

Prove that `1 ∈ ({1, 2, 3} : Finset Nat)`.

Since `{1, 2, 3}` is `insert 1 (insert 2 {3})`, and `1` equals the
outermost inserted element, this should be straightforward.

**Strategy**: Rewrite with `Finset.mem_insert` to turn the membership
question into a disjunction `1 = 1 ∨ 1 ∈ insert 2 {3}`. Then take the
left branch with `left` and close with `rfl`.
"

/-- `1` is an element of `{1, 2, 3}`. -/
Statement : 1 ∈ ({1, 2, 3} : Finset Nat) := by
  Hint "The goal asks whether `1` belongs to the finset containing 1, 2, 3.
  Recall that this finset is really `insert 1 (insert 2 (singleton 3))`.
  Use `Finset.mem_insert` to break the membership question into
  `1 = 1 ∨ 1 ∈ insert 2 (singleton 3)`."
  Hint (hidden := true) "Use `rw [Finset.mem_insert]` to rewrite the goal."
  rw [Finset.mem_insert]
  Hint "The goal is now a disjunction: `1 = 1` or `1` belongs to the
  inner finset. Since `1 = 1` is true, choose the left disjunct."
  Hint (hidden := true) "Use `left` to choose the left disjunct, then `rfl`."
  left
  rfl

Conclusion
"
You just proved your first membership fact! The proof followed a simple
pattern:

1. **Rewrite** with `Finset.mem_insert` to expose the disjunction.
2. **Choose a branch** with `left` or `right`.
3. **Close** with `rfl` when the element matches the inserted value.

This pattern will recur throughout the world. The key insight is that
membership in a finset built by `insert` always reduces to an `∨`:
either the element is the one that was just inserted, or it was already
in the smaller finset.

**In plain language**: \"To show that 1 is in {1, 2, 3}, observe that 1
is the first element listed.\"
"

/-- `Finset.mem_insert` states that `a ∈ insert b s ↔ a = b ∨ a ∈ s`.

An element belongs to `insert b s` exactly when it equals `b` or it
already belonged to `s`. This is the fundamental lemma for reasoning
about membership in finsets built by `insert`. -/
TheoremDoc Finset.mem_insert as "Finset.mem_insert" in "Finset"

NewTheorem Finset.mem_insert
DisabledTactic trivial decide native_decide simp aesop simp_all
