import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 2

Title "Deeper membership: reaching past the first insert"

Introduction
"
# What if the element is not the outermost one?

In the previous level, `1` was the outermost inserted element of
`insert 1 (insert 2 {3})`, so one application of `mem_insert` plus
`left` was enough.

But what about `2 ∈ {1, 2, 3}`? Now `2` is *not* the outermost
element -- it is buried one level deeper.

## The search pattern

After `rw [Finset.mem_insert]`, you get `2 = 1 ∨ 2 ∈ insert 2 {3}`.
Since `2 ≠ 1`, the left branch is a dead end. Choose `right` to enter
the inner finset `insert 2 {3}`, then apply `mem_insert` again to find
`2` at the next layer.

## Your task

Prove that `2 ∈ ({1, 2, 3} : Finset Nat)`. You will need to apply
`Finset.mem_insert` twice -- once to pass the outer `insert 1`, and
once to match at the inner `insert 2`.
"

/-- `2` is an element of `{1, 2, 3}`. -/
Statement : 2 ∈ ({1, 2, 3} : Finset Nat) := by
  Hint "The finset is `insert 1 (insert 2 (singleton 3))`.
  Rewrite with `Finset.mem_insert` to ask: is `2 = 1`, or is
  `2` in the inner finset `insert 2 (singleton 3)`?"
  Hint (hidden := true) "Use `rw [Finset.mem_insert]`."
  rw [Finset.mem_insert]
  Hint "The goal is `2 = 1 ∨ 2 ∈ insert 2 (singleton 3)`. Since `2 ≠ 1`,
  choose the right branch."
  Hint (hidden := true) "Use `right`."
  right
  Hint "Now the goal is `2 ∈ insert 2 (singleton 3)`. Apply `mem_insert` again
  to find `2` as the outermost inserted element."
  Hint (hidden := true) "Use `rw [Finset.mem_insert]` again, then `left`
  and `rfl`."
  rw [Finset.mem_insert]
  left
  rfl

Conclusion
"
To find `2` in `{1, 2, 3}`, you had to **search past** the outermost
`insert 1` by choosing `right`, then find `2` at the next `insert 2`
layer by choosing `left`.

This is a general pattern: to prove `a ∈ {x₁, x₂, ..., xₙ}`, apply
`mem_insert` at each layer and choose `left` when `a` matches the
inserted element, or `right` to keep searching deeper.

**Think of it as scanning a list from left to right**: \"Is `2` equal to
`1`? No. Is `2` equal to `2`? Yes.\"

Notice that this manual search is tedious for large finsets. If you had
to prove `100 ∈ {1, 2, ..., 100}`, you would need 99 applications of
`right` followed by one `left`. Later in this world, you will learn
a tactic that automates this search entirely.

**In plain language**: \"To show 2 is in {1, 2, 3}, scan the elements:
2 is not 1, but 2 is 2 -- found it.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all
