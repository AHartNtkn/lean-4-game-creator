import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 4

Title "Introducing simp with finset lemmas"

Introduction
"
# Automating membership proofs with `simp`

The manual proof pattern from the first three levels works, but it is
tedious: for each `insert` layer you must rewrite, choose a branch,
and close with `rfl`. For `2 ∈ {1, 2, 3}` this was 5 tactic steps.
For `50 ∈ {1, 2, ..., 50}` it would be 99 steps.

## `simp` with a lemma list

The tactic `simp` can apply a collection of rewrite rules repeatedly
until no more apply. When you give it the right membership lemmas, it
automates the entire search:

```
simp [Finset.mem_insert, Finset.mem_singleton]
```

This tells `simp` to use both `mem_insert` and `mem_singleton` as
simplification rules. It will:
1. Unfold each `insert` layer (via `mem_insert`).
2. Resolve the singleton base (via `mem_singleton`).
3. Close any resulting `a = a` goals automatically.

## Your task

Prove that `2 ∈ ({1, 2, 3} : Finset Nat)` using `simp` with the
two finset membership lemmas.

In this level, `simp` is available -- use it!
"

/-- `2` is an element of `{1, 2, 3}`, proved with `simp`. -/
Statement : 2 ∈ ({1, 2, 3} : Finset Nat) := by
  Hint "Instead of the manual `rw`/`left`/`right` pattern, try using
  `simp` with the membership lemmas. You need both `Finset.mem_insert`
  (for the `insert` layers) and `Finset.mem_singleton` (for the base)."
  Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
  simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
One tactic call replaced the five-step manual proof from Level 2.
This is the power of `simp` with a lemma list: it automates chains
of rewrites that follow a predictable pattern.

## How `simp` works here

`simp [Finset.mem_insert, Finset.mem_singleton]` repeatedly applies
both lemmas as rewrite rules:

1. `2 ∈ insert 1 (insert 2 {3})` is rewritten to
   `2 = 1 ∨ 2 ∈ insert 2 {3}`
2. The `2 = 1` is simplified to `False` (since `2 ≠ 1`)
3. `2 ∈ insert 2 {3}` is rewritten to `2 = 2 ∨ 2 ∈ {3}`
4. The `2 = 2` is simplified to `True`
5. `False ∨ True` simplifies to `True` -- done.

## When to use `simp` with finset lemmas

This pattern is ideal for **concrete membership goals** where the
elements and the finset are all known values. It does not require
any creativity from the prover -- it is pure computation.

**In plain language**: \"Checking whether 2 is in {1, 2, 3} is a
mechanical scan. The `simp` tactic automates exactly this kind
of mechanical verification.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
