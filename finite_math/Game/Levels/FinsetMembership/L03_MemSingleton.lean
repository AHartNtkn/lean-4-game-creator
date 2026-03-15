import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 3

Title "Membership in a singleton"

Introduction
"
# The base case: `Finset.mem_singleton`

When you search for an element using `Finset.mem_insert`, you eventually
reach the innermost finset -- a singleton `{a}`. At that point you need
a lemma for membership in singletons:

```
Finset.mem_singleton : b ∈ {a} ↔ b = a
```

This says: the only element of `{a}` is `a` itself.

## Completing the search

Together, `mem_insert` and `mem_singleton` let you prove any concrete
membership fact by repeated rewriting:

- `mem_insert` handles each `insert` layer: \"is `x` equal to the
  inserted element, or should we search deeper?\"
- `mem_singleton` handles the innermost layer: \"is `x` equal to the
  last element?\"

## Your task

Prove that `3 ∈ ({1, 2, 3} : Finset Nat)`.

Since `3` is the innermost element (recall `{1, 2, 3}` is
`insert 1 (insert 2 {3})`), you will need to pass through both
`insert` layers with `right`, then use `mem_singleton` at the base.
"

/-- `3` is an element of `{1, 2, 3}`. -/
Statement : 3 ∈ ({1, 2, 3} : Finset Nat) := by
  Hint "The finset is `insert 1 (insert 2 (singleton 3))`.
  To find `3`, you need to search past both `insert` layers."
  Hint (hidden := true) "Start with `rw [Finset.mem_insert]` and choose `right`."
  rw [Finset.mem_insert]
  right
  Hint "Now the goal is `3 ∈ insert 2 (singleton 3)`. Search past this layer too."
  Hint (hidden := true) "Use `rw [Finset.mem_insert]` again and choose `right`."
  rw [Finset.mem_insert]
  right
  Hint "The goal is `3 ∈` a singleton containing just `3`. Use the lemma
  `Finset.mem_singleton` which says `b ∈ singleton a ↔ b = a`."
  Hint (hidden := true) "Use `rw [Finset.mem_singleton]`."
  rw [Finset.mem_singleton]

Conclusion
"
You have now seen the complete manual proof pattern for membership in
literal finsets:

1. **Peel** each `insert` layer with `rw [Finset.mem_insert]`.
2. At each layer, choose `left` (if the element matches) or `right`
   (to search deeper).
3. At the **singleton base**, use `rw [Finset.mem_singleton]`.

This is systematic but verbose. For `3 ∈ {1, 2, 3}`, you needed:
- Two `rw [Finset.mem_insert]` steps (both choosing `right`)
- One `rw [Finset.mem_singleton]` at the base

For a finset with $n$ elements, the worst case requires $n - 1$
applications of `mem_insert` plus one `mem_singleton`.

The next level will introduce a tactic that does all of this
automatically.

**In plain language**: \"To show 3 is in {1, 2, 3}, scan past 1 and 2,
then find 3 at the end.\"
"

/-- `Finset.mem_singleton` states that `b ∈ {a} ↔ b = a`.

The only element of a singleton finset `{a}` is `a` itself.
This is the base case for membership proofs in literal finsets. -/
TheoremDoc Finset.mem_singleton as "Finset.mem_singleton" in "Finset"

NewTheorem Finset.mem_singleton
DisabledTactic trivial decide native_decide simp aesop simp_all
