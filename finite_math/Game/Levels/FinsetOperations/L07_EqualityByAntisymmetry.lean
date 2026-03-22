import Game.Metadata

World "FinsetOperations"
Level 7

Title "Equality by Mutual Containment"

Introduction "
# Equality: The Hard Way

When are two finsets equal? One approach: show that each is a subset
of the other. If $A \\subseteq B$ and $B \\subseteq A$, then $A = B$.

In Lean, this is `Finset.Subset.antisymm`:
```
Finset.Subset.antisymm : s ⊆ t → t ⊆ s → s = t
```

The proof move: `apply Finset.Subset.antisymm` on a goal `s = t`
creates two subgoals: `s ⊆ t` and `t ⊆ s`. You then prove each
subset using `subset_iff` and element chasing from the previous level.

**Your task**: Prove that $\\{1, 2\\} = \\{2, 1\\}$.

This is 'obvious' — the sets have the same elements. But Lean requires
a proof. Using `Subset.antisymm`, you must show containment in
*both* directions.
"

/-- {1, 2} = {2, 1} by mutual containment. -/
Statement : ({1, 2} : Finset ℕ) = {2, 1} := by
  Hint "**This level is deliberately tedious.** The next level introduces
  `ext`, a much cleaner approach. The verbosity here motivates why `ext`
  is valuable."
  Hint "Use `apply Finset.Subset.antisymm` to split the equality
  into two subset goals."
  apply Finset.Subset.antisymm
  -- Forward: {1, 2} ⊆ {2, 1}
  · Hint "Prove the first subset direction. Start with
    `rw [Finset.subset_iff]` and `intro x hx`."
    rw [Finset.subset_iff]
    intro x hx
    Hint (hidden := true) "Unfold `hx` with
    `rw [Finset.mem_insert, Finset.mem_singleton] at hx`, then
    case split."
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h =>
      rw [h]
      rw [Finset.mem_insert]
      right
      rw [Finset.mem_singleton]
    | inr h =>
      rw [h]
      rw [Finset.mem_insert]
      left
      rfl
  -- Backward: {2, 1} ⊆ {1, 2}
  · Hint "Now the reverse direction.
    Same pattern: `rw [Finset.subset_iff]; intro x hx`."
    rw [Finset.subset_iff]
    intro x hx
    Hint (hidden := true) "Unfold `hx` with
    `rw [Finset.mem_insert, Finset.mem_singleton] at hx`, then
    case split with `cases hx with`."
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h =>
      Hint (hidden := true) "`rw [{h}]; rw [Finset.mem_insert]; right; rw [Finset.mem_singleton]`."
      rw [h]
      rw [Finset.mem_insert]
      right
      rw [Finset.mem_singleton]
    | inr h =>
      Hint (hidden := true) "`rw [{h}]; rw [Finset.mem_insert]; left; rfl`."
      rw [h]
      rw [Finset.mem_insert]
      left
      rfl

Conclusion "
That was a lot of work for something 'obvious.' The proof has
**four** element-chasing branches (two elements × two directions).

Notice the boilerplate: both directions are nearly identical because
`{{1, 2}}` and `{{2, 1}}` have the same elements — the only difference
is the order.

This motivates a cleaner approach: instead of proving containment
in both directions, what if we could directly show that two finsets
have the same elements? That's the `ext` tactic, coming in the
next level.

In plain mathematics, this proof uses the fact that
$A = B \\iff A \\subseteq B \\land B \\subseteq A$. It's valid but verbose.
"

/-- `Finset.Subset.antisymm` proves that if `s ⊆ t` and `t ⊆ s`,
then `s = t`.

## Syntax
```
apply Finset.Subset.antisymm
```
This changes the goal from `s = t` to two subgoals: `s ⊆ t` and `t ⊆ s`.

## When to use it
When you want to prove two finsets are equal by showing mutual containment.

## Example
```
-- Goal: {1, 2} = {2, 1}
apply Finset.Subset.antisymm
-- Goal 1: {1, 2} ⊆ {2, 1}
-- Goal 2: {2, 1} ⊆ {1, 2}
```

## Note
This approach works but can be verbose. For a cleaner alternative,
see the `ext` tactic.
-/
TheoremDoc Finset.Subset.antisymm as "Finset.Subset.antisymm" in "Finset"

NewTheorem Finset.Subset.antisymm

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm Finset.pair_comm le_antisymm Finset.insert_comm
