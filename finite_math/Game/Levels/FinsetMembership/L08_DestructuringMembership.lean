import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 8

Title "Destructuring membership"

Introduction
"
# Case-splitting on a membership hypothesis

So far you have proved concrete membership facts: specific numbers in
specific finsets. But what about **symbolic** membership? When you have
a hypothesis `h : x ∈ insert a s` where `x` is a *variable*, you
cannot just use `simp` -- you need to reason about what `x` could be.

## Rewriting hypotheses with `at`

You already know `rw [Finset.mem_insert]` rewrites the **goal**. But
you can also rewrite a **hypothesis**:

```
rw [Finset.mem_insert] at h
```

This transforms `h : x ∈ insert a s` into `h : x = a ∨ x ∈ s`.

## Case-splitting with `rcases`

Once `h` is a disjunction `x = a ∨ x ∈ s`, you can case-split:

```
rcases h with rfl | hmem
```

This creates two goals:
- In the first, `rfl` substitutes `a` for `x` everywhere. The variable
  `x` disappears and is replaced by `a`.
- In the second, `hmem : x ∈ s` gives you the membership in the
  smaller finset.

## Your task

Given `x : Nat` and `h : x ∈ ({1, 2, 3} : Finset Nat)`, prove that
`x < 4`.

**Strategy**: Rewrite `h` with `mem_insert`, case-split with `rcases`,
and close each case with `omega`.
"

/-- If `x ∈ {1, 2, 3}`, then `x < 4`. -/
Statement (x : Nat) (h : x ∈ ({1, 2, 3} : Finset Nat)) : x < 4 := by
  Hint "You have `h` saying `x` belongs to the finset containing 1, 2, 3.
  This finset is `insert 1 (insert 2 (singleton 3))`. Rewrite `h` using
  `mem_insert` to turn it into a disjunction."
  Hint (hidden := true) "Use `rw [Finset.mem_insert] at h`."
  rw [Finset.mem_insert] at h
  Hint "Now `h` is a disjunction: `x = 1 ∨ x ∈ insert 2 (singleton 3)`.
  Use `rcases` to split into the two cases. Using `rfl` for the
  equality case will substitute `1` for `x`."
  Hint (hidden := true) "Use `rcases h with rfl | h`."
  rcases h with rfl | h
  · Hint "In this case, `x` has been replaced by `1` and the goal is
    `1 < 4`. This is a concrete arithmetic fact."
    Hint (hidden := true) "Use `omega`."
    omega
  · Hint "Now `h` says `x` belongs to `insert 2 (singleton 3)`. Rewrite
    again with `mem_insert` to peel another layer."
    Hint (hidden := true) "Use `rw [Finset.mem_insert] at h` and
    `rcases h with rfl | h` again."
    rw [Finset.mem_insert] at h
    rcases h with rfl | h
    · Hint "Now `x = 2` and the goal is `2 < 4`."
      Hint (hidden := true) "Use `omega`."
      omega
    · Hint "Now `h` says `x` belongs to the singleton containing 3.
      Use `mem_singleton` to extract the equality."
      Hint (hidden := true) "Use `rw [Finset.mem_singleton] at h`.
      Now `h : x = 3`. Use `rcases h with rfl` to substitute, then
      `omega`."
      rw [Finset.mem_singleton] at h
      rcases h with rfl
      omega

Conclusion
"
You just performed **exhaustive case analysis on finset membership**.
Given `x ∈ {1, 2, 3}`, there are only three possibilities for `x`:
it is 1, 2, or 3. The proof systematically considered each case.

## The proof pattern

1. `rw [Finset.mem_insert] at h` -- turn membership into a disjunction.
2. `rcases h with rfl | h` -- split into \"element matches\" or
   \"search deeper\".
3. In the `rfl` case, `x` is replaced by the concrete value and the
   goal becomes purely arithmetic.
4. In the `h` case, repeat from step 1 on the smaller finset.
5. At the singleton base, `rw [Finset.mem_singleton] at h` followed by
   `rcases h with rfl` handles the last case.

## When you need this

This pattern is essential whenever you need to prove a **property**
of an unknown element that belongs to a finite set. Since the finset
has finitely many elements, you can check each one.

**In plain language**: \"If `x` is in {1, 2, 3}, then `x` is 1, 2, or 3.
In each case, `x < 4`.\" This is proof by exhaustion -- the hallmark
of finite reasoning.
"

/-- `rcases` splits a hypothesis into cases. Given a disjunction `h : P ∨ Q`,
`rcases h with hp | hq` creates two goals: one with `hp : P` and one with `hq : Q`.

The special pattern `rfl` substitutes the equality immediately:
`rcases h with rfl | hq` replaces the variable with the concrete value
in the first branch.

`rcases` also works on conjunctions, existentials, and nested patterns. -/
TacticDoc rcases

NewTactic rcases
DisabledTactic trivial decide native_decide aesop simp_all
