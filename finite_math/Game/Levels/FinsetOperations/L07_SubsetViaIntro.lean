import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 7

Title "Subset via intro"

Introduction
"
# Proving subset relations

A finset `s` is a **subset** of `t`, written `s ⊆ t`, when every
element of `s` is also an element of `t`:

```
Finset.subset_iff : s ⊆ t ↔ ∀ ⦃a⦄, a ∈ s → a ∈ t
```

In practice, `s ⊆ t` **unfolds** to `∀ a, a ∈ s → a ∈ t`. So to prove
a subset relation, you introduce an element and a membership hypothesis,
then show the element belongs to the larger finset.

## Notation

The symbol `⊆` is typed `\\sub` or `\\subseteq`.

## Your task

Prove that `s ⊆ s ∪ t` for arbitrary finsets `s` and `t`. This says
that every finset is a subset of its union with any other finset.

**Strategy**: Introduce `a` and `ha : a ∈ s`, then show `a ∈ s ∪ t`
by rewriting with `mem_union` and choosing the left branch.
"

/-- Every finset is a subset of its union with another. -/
Statement (s t : Finset Nat) : s ⊆ s ∪ t := by
  Hint "The goal is `s ⊆ s ∪ t`. Since `⊆` means \"every element of
  the left is in the right\", start by introducing an arbitrary element
  and its membership hypothesis."
  Hint (hidden := true) "Use `intro a ha`."
  intro a ha
  Hint "Now you have `ha : a ∈ s` and need to show `a ∈ s ∪ t`.
  Rewrite the goal with `mem_union` to get a disjunction."
  Hint (hidden := true) "Use `rw [Finset.mem_union]`."
  rw [Finset.mem_union]
  Hint "The goal is `a ∈ s ∨ a ∈ t`. Since you already know `a ∈ s`,
  choose the left branch."
  Hint (hidden := true) "Use `left`, then `exact ha`."
  left
  exact ha

Conclusion
"
You proved that `s ⊆ s ∪ t` -- every finset is a subset of its union
with any other finset. The proof pattern for subset relations is:

1. **Introduce** an element `a` and its membership `ha : a ∈ s`.
2. **Show** `a` belongs to the target finset.

This is the same as the standard mathematical proof:

> \"Let a ∈ s. Then a ∈ s ∨ a ∈ t, so a ∈ s ∪ t.\"

## When `⊆` appears

Subset proofs always start with `intro a ha` (or `intro a` then
`intro ha`). The `⊆` notation unpacks to a universal statement
about membership, just as in ordinary set theory.

**In plain language**: \"s ⊆ s ∪ t because any element of s is
automatically in s ∪ t (it belongs to the first part of the union).\"
"

DisabledTactic trivial decide native_decide aesop simp_all
