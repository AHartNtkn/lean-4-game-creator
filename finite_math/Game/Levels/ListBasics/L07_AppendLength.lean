import GameServer.Commands
import Mathlib

World "ListBasics"
Level 7

Title "Length of an append"

Introduction
"
# Reasoning about append and length

You have now learned the key membership lemmas for lists. In this level,
you will practice **rewriting** with list lemmas -- a proof move you know
well from the Natural Number Game.

## The key lemma

The length of a concatenation is the sum of the lengths:
```
List.length_append : (l₁ ++ l₂).length = l₁.length + l₂.length
```

## Your task

Given two lists `l₁` and `l₂`, prove that `(l₁ ++ l₂).length = l₁.length + l₂.length`.

This is a direct application of the lemma. Use `rw [List.length_append]` --
and the goal closes immediately!

This level practices the pattern: **rewrite with a structural lemma
to transform the goal**.
"

/-- The length of a concatenation equals the sum of the individual lengths. -/
Statement (l₁ l₂ : List Nat) : (l₁ ++ l₂).length = l₁.length + l₂.length := by
  Hint "Use `rw [List.length_append]` to rewrite the length of the
  concatenation as the sum of individual lengths."
  rw [List.length_append]

DisabledTactic decide native_decide simp aesop

Conclusion
"
After rewriting with `List.length_append`, the goal became
`l₁.length + l₂.length = l₁.length + l₂.length`, and Lean closed it
automatically.

This is the standard pattern for using API lemmas:
1. Find the relevant lemma (here, `List.length_append`)
2. Rewrite with it to transform the goal into a simpler form
3. Handle the resulting subgoal (here, trivially `rfl`)

**Important**: The lemma `List.length_append` works for **any** two lists.
Whether the lists are concrete or symbolic, the rewrite produces
`l₁.length + l₂.length`.

**In plain language**: \"The number of elements in a concatenation equals
the sum of the element counts of the two pieces.\"
"

/-- `List.length_append` states that
`(l₁ ++ l₂).length = l₁.length + l₂.length`.
The length of a concatenation is the sum of the individual lengths. -/
TheoremDoc List.length_append as "List.length_append" in "List"

NewTheorem List.length_append
