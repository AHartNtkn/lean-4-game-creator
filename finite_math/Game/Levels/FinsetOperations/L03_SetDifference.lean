import Game.Metadata

World "FinsetOperations"
Level 3

Title "Set Difference"

Introduction "
# Set Difference: In One But Not the Other

The **set difference** `s \\ t` contains elements that are in `s`
but *not* in `t`. The membership characterization is:

$$a \\in s \\setminus t \\;\\longleftrightarrow\\; a \\in s \\;\\land\\; a \\notin t$$

In Lean, this is `Finset.mem_sdiff`:
```
Finset.mem_sdiff : a ∈ s \\ t ↔ a ∈ s ∧ a ∉ t
```

The proof move: `rw [Finset.mem_sdiff]` converts a set-difference
membership goal into a conjunction. The first part (`a ∈ s`) is a
standard membership proof. The second part (`a ∉ t`) is a
*non-membership* proof — assume `a ∈ t`, then derive a contradiction.

**Your task**: Prove that $1 \\in \\{1, 2, 3\\} \\setminus \\{2, 4\\}$.
"

/-- 1 is in {1, 2, 3} \ {2, 4}. -/
Statement : (1 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) \ {2, 4} := by
  Hint "Use `rw [Finset.mem_sdiff]` to convert the set-difference
  membership into a conjunction."
  rw [Finset.mem_sdiff]
  Hint "The goal is a conjunction: `1` is in the left set AND `1` is
  NOT in the right set. Use `constructor` to split into two goals."
  constructor
  · Hint "Prove membership in the first set — this is a standard membership proof."
    Hint (hidden := true) "`rw [Finset.mem_insert]; left; rfl`."
    rw [Finset.mem_insert]
    left
    rfl
  · Hint "Prove non-membership in the second set. Use `intro h` to
    assume membership, then derive a contradiction."
    intro h
    Hint "Unfold the hypothesis with `rw [Finset.mem_insert, Finset.mem_singleton] at h`.
    This gives `h : 1 = 2 ∨ 1 = 4`. Then `omega` closes the
    contradiction (neither `1 = 2` nor `1 = 4`)."
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    omega

Conclusion "
Set difference adds a new twist: you need *non-membership*, not just
membership. The non-membership proof follows the pattern from
Finset Basics:

1. `intro h` — assume the element *is* a member
2. `rw [Finset.mem_insert, ...] at h` — unfold the membership
3. `omega` — show the resulting equalities are contradictory

The conjunction `a ∈ s ∧ a ∉ t` combines two moves you already know:
- **Membership**: `rw [mem_insert]; left; rfl` (or similar)
- **Non-membership**: `intro h; rw [...] at h; omega`

In plain mathematics: $x \\in A \\setminus B$ means $x \\in A$ and $x \\notin B$.

**Warning**: Unlike union and intersection, set difference is
**not commutative**. For example, $\\{1, 2\\} \\setminus \\{2, 3\\} = \\{1\\}$
but $\\{2, 3\\} \\setminus \\{1, 2\\} = \\{3\\}$ — different results! The
order matters because 'elements in $A$ but not in $B$' is a fundamentally
asymmetric condition.
"

/-- `Finset.mem_sdiff` states that `a ∈ s \\ t ↔ a ∈ s ∧ a ∉ t`.

## Syntax
```
rw [Finset.mem_sdiff]       -- in the goal
rw [Finset.mem_sdiff] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis involves `x ∈ s \\ t` (set difference).
After rewriting, the goal becomes a conjunction: membership in `s`
and non-membership in `t`.

## Example
```
-- Goal: 1 ∈ {1, 2, 3} \\ {2, 4}
rw [Finset.mem_sdiff]
-- Goal: 1 ∈ {1, 2, 3} ∧ 1 ∉ {2, 4}
constructor
-- Two subgoals: prove membership and non-membership
```
-/
TheoremDoc Finset.mem_sdiff as "Finset.mem_sdiff" in "Finset"

/-- `Finset.sdiff s t` (written `s \\ t`) is the finset containing all
elements of `s` that are not in `t`.

## Notation
`s \\ t` — the set difference (elements in `s` but not in `t`).

## Key lemma
`Finset.mem_sdiff : a ∈ s \\ t ↔ a ∈ s ∧ a ∉ t`

## Warning
Set difference is NOT symmetric: `s \\ t ≠ t \\ s` in general.
-/
DefinitionDoc Finset.sdiff as "Finset.sdiff"

NewDefinition Finset.sdiff
NewTheorem Finset.mem_sdiff

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem
