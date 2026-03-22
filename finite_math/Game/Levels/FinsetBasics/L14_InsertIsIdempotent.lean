import Game.Metadata

World "FinsetBasics"
Level 14

Title "Insert is Idempotent"

Introduction "
# Insert is Idempotent

Here's a common misconception: inserting an element always makes the
set bigger. **Wrong.** Finsets have no duplicates, so inserting an
element that's already present does nothing.

The formal statement is `Finset.insert_eq_of_mem`:

$$a \\in s \\;\\longrightarrow\\; \\texttt{insert } a \\; s = s$$

Notice this is an **implication**, not an iff. The direction matters:
- If `a ∈ s`, then `insert a s = s` (idempotent)
- If `a ∉ s`, then `insert a s ≠ s` (the set grows by one element)

To use `insert_eq_of_mem`, you `apply` it. This changes the goal from
an equation (`insert a s = s`) to a membership proof (`a ∈ s`). Then
you prove membership using the `mem_insert`/`mem_singleton` chain
from earlier levels.

**Your task**: Prove that `insert 2 {1, 2, 3} = {1, 2, 3}`.
"

/-- Inserting 2 into {1, 2, 3} gives back {1, 2, 3}. -/
Statement : insert 2 ({1, 2, 3} : Finset ℕ) = {1, 2, 3} := by
  Hint "Use `apply Finset.insert_eq_of_mem` to reduce the equation to
  a membership proof."
  apply Finset.insert_eq_of_mem
  Hint "Now prove that `2` is a member of the set. Peel the inserts:
  `rw [Finset.mem_insert]`, then `right`,
  then `rw [Finset.mem_insert]`, then `left; rfl`."
  Hint (hidden := true) "First `rw [Finset.mem_insert]` gives a disjunction
  `2 = 1 ∨ ...`. Take `right`. Then `rw [Finset.mem_insert]` gives
  `2 = 2 ∨ ...`. Take `left; rfl`."
  rw [Finset.mem_insert]
  right
  rw [Finset.mem_insert]
  left
  rfl

Conclusion "
The proof has two stages:
1. `apply Finset.insert_eq_of_mem` — reduce the equation to membership
2. Prove membership using the `mem_insert`/`mem_singleton` chain

This is the **apply-then-prove** pattern: use `apply` with a theorem
whose conclusion matches the goal, and the theorem's premise becomes
your new goal. Here, `apply insert_eq_of_mem` matches the goal
`insert a s = s` and leaves the premise `a ∈ s` to prove.

This pattern recurs throughout mathematics in Lean. Whenever a
theorem's conclusion matches your goal, `apply` it — and the premise
becomes your new goal. Watch for this pattern in future worlds.

In plain mathematics, $\\{2\\} \\cup \\{1, 2, 3\\} = \\{1, 2, 3\\}$ is
obvious because 2 is already in the set. In Lean, you must *prove*
the membership to justify the equality.
"

/-- `Finset.insert_eq_of_mem` states that if `a ∈ s`, then
`insert a s = s`.

Inserting an element that's already present is a no-op.

## Syntax
```
apply Finset.insert_eq_of_mem
```
This changes the goal from `insert a s = s` to `a ∈ s`.

## When to use it
When you need to prove that inserting a duplicate element
doesn't change the finset.

## Example
```
-- Goal: insert 2 {1, 2, 3} = {1, 2, 3}
apply Finset.insert_eq_of_mem
-- Goal: 2 ∈ {1, 2, 3}
```

## Warning
This only works when `a` is already in `s`. If `a ∉ s`,
the insertion genuinely changes the set.
-/
TheoremDoc Finset.insert_eq_of_mem as "Finset.insert_eq_of_mem" in "Finset"

NewTheorem Finset.insert_eq_of_mem

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem
