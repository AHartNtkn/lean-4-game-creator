import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 5

Title "simp vs manual rewriting"

Introduction
"
# When to use `simp` and when to rewrite manually

You now have two tools for proving membership:

1. **Manual rewriting**: `rw [Finset.mem_insert]`, choose a branch,
   repeat until `mem_singleton` closes the goal.
2. **Automated search**: `simp [Finset.mem_insert, Finset.mem_singleton]`.

Both work for concrete membership goals. But they have different
strengths:

- `simp` is **fast and convenient** for concrete goals where all values
  are known. It automates the boring search.
- Manual `rw` gives **fine control** over the proof state. This matters
  when you need to reason *about* membership (e.g., case-splitting on
  which element `x` is) rather than just verifying it.

## Your task

Prove that `3 ∈ insert 1 (insert 2 ({3, 4} : Finset Nat))`.

This is a deeper membership fact -- `3` is buried under two explicit
`insert` calls plus the notation `{3, 4}` (which is itself
`insert 3 {4}`).

Use `simp` with the membership lemmas to close it in one step.
"

/-- `3` belongs to `insert 1 (insert 2 {3, 4})`. -/
Statement : 3 ∈ insert 1 (insert 2 ({3, 4} : Finset Nat)) := by
  Hint "This is a concrete membership goal. All elements are known
  natural numbers. The `simp` tactic with finset membership lemmas can
  handle this automatically."
  Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
  simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
`simp` handled the entire chain: four `insert` layers
(two explicit, two from `{3, 4}` notation) plus the singleton base,
all in one call.

## The general rule

For **concrete membership verification** (all elements are specific
values), `simp [Finset.mem_insert, Finset.mem_singleton]` is the right
tool. It scales to any finset size.

For **symbolic membership reasoning** (the element or the finset
contains variables), you will often need manual rewriting because
`simp` cannot evaluate `x = 1` without knowing `x`. You will see
this distinction in later levels of this world.

## Efficiency note

You might wonder: if `simp` can do it all, why learn the manual
approach? Three reasons:

1. The manual approach **explains what `simp` is doing** -- without it,
   `simp` would be a black box.
2. Manual rewriting is needed for **symbolic goals** (coming soon).
3. Understanding the structure helps you **debug** when `simp` fails.

**In plain language**: \"For routine membership checks with specific
numbers, let the automation do the work. Save manual reasoning for
when you need to understand *why* something is a member, not just
*that* it is.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
