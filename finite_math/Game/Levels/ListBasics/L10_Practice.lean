import GameServer.Commands
import Mathlib

World "ListBasics"
Level 10

Title "Backward membership reasoning"

Introduction
"
# Analyzing a membership hypothesis

In every level so far, you have **built** membership proofs from
scratch -- rewriting the goal, choosing branches, and closing with
a hypothesis. This is **forward** reasoning: you transform the goal
until it matches something you know.

But sometimes you start with a membership hypothesis and need to
**take it apart**. If you know `h : a ∈ l₁ ++ l₂`, what can you
conclude? By `List.mem_append`, this means `a ∈ l₁ ∨ a ∈ l₂`.

## Rewriting a hypothesis

You already know `rw [lemma]` rewrites the **goal**. To rewrite
a **hypothesis** `h` instead, write:
```
rw [lemma] at h
```

After `rw [List.mem_append] at h`, the hypothesis `h : a ∈ l₁ ++ l₂`
becomes `h : a ∈ l₁ ∨ a ∈ l₂`.

## Case-splitting with `rcases`

When a hypothesis is a disjunction `h : P ∨ Q`, you can split into
two cases with:
```
rcases h with h₁ | h₂
```

This creates two subgoals: one where `h₁ : P`, and one where `h₂ : Q`.
You prove the goal separately in each case.

## Your task

Prove that membership in an append is symmetric: if `a ∈ l₁ ++ l₂`,
then `a ∈ l₂ ++ l₁`.

**Strategy**:
1. `rw [List.mem_append] at h` to unfold the hypothesis into a disjunction
2. `rcases h with h₁ | h₂` to split into cases
3. In each case, `rw [List.mem_append]` on the goal, choose the right
   branch (`left` or `right`), and close with `exact`
"

/-- If `a ∈ l₁ ++ l₂`, then `a ∈ l₂ ++ l₁`. -/
Statement (a : Nat) (l₁ l₂ : List Nat) (h : a ∈ l₁ ++ l₂) :
    a ∈ l₂ ++ l₁ := by
  Hint "The hypothesis `h : a ∈ l₁ ++ l₂` needs to be unfolded.
  Rewrite **the hypothesis** (not the goal) with
  `rw [List.mem_append] at h`."
  rw [List.mem_append] at h
  Hint "Now `h : a ∈ l₁ ∨ a ∈ l₂`. Split into two cases with
  `rcases h with h₁ | h₂`."
  rcases h with h₁ | h₂
  · Hint "In this case, `h₁ : a ∈ l₁`. You need `a ∈ l₂ ++ l₁`.
    Unfold the goal with `rw [List.mem_append]`."
    rw [List.mem_append]
    Hint "The goal is `a ∈ l₂ ∨ a ∈ l₁`. The element is in `l₁`,
    so take the right branch with `right`."
    right
    Hint "The goal is `a ∈ l₁`, which is `h₁`. Close with `exact h₁`."
    exact h₁
  · Hint "In this case, `h₂ : a ∈ l₂`. Unfold the goal with
    `rw [List.mem_append]`."
    rw [List.mem_append]
    Hint "The goal is `a ∈ l₂ ∨ a ∈ l₁`. The element is in `l₂`,
    so take the left branch with `left`."
    left
    Hint "The goal is `a ∈ l₂`, which is `h₂`. Close with `exact h₂`."
    exact h₂

DisabledTactic decide native_decide simp aesop

Conclusion
"
You proved that membership in an append is symmetric: if an element
is in `l₁ ++ l₂`, it is also in `l₂ ++ l₁`.

This level introduced two important new skills:

1. **Rewriting hypotheses**: `rw [lemma] at h` transforms a hypothesis
   instead of the goal. This is the backward counterpart of the `rw`
   you already know. Any `rw` that works on the goal can also be
   applied to a hypothesis using `at`.

2. **Case-splitting on disjunctions**: `rcases h with h₁ | h₂` splits
   a hypothesis `h : P ∨ Q` into two subgoals -- one where `h₁ : P`,
   and one where `h₂ : Q`. You name the new hypotheses yourself.

Together, these let you **analyze** membership hypotheses, not just
**construct** membership goals. You can now reason in both directions.

**In plain language**: \"If $a$ appears somewhere in the concatenation
$l_1 {++} l_2$, then it must be in either $l_1$ or $l_2$ -- and either
way, it appears in $l_2 {++} l_1$.\"
"

/-- `rcases h with h₁ | h₂` splits a disjunction hypothesis `h : P ∨ Q`
into two subgoals: one with `h₁ : P` and one with `h₂ : Q`.

More generally, `rcases` can destructure any inductive hypothesis. For
conjunctions, use `⟨h₁, h₂⟩`; for disjunctions, use `h₁ | h₂`. -/
TacticDoc rcases

NewTactic rcases
