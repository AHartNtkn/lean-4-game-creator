import Game.Metadata

World "FinsetOperations"
Level 1

Title "Union Membership"

Introduction "
# Union: Combining Two Finsets

The **union** `s ∪ t` contains every element that belongs to `s`, to `t`,
or to both. The membership characterization is:

$$a \\in s \\cup t \\;\\longleftrightarrow\\; a \\in s \\;\\lor\\; a \\in t$$

In Lean, this is `Finset.mem_union`:
```
Finset.mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t
```

The proof move: `rw [Finset.mem_union]` converts a union membership goal
into a disjunction. Then you choose `left` or `right` and prove membership
in the appropriate piece.

**Note**: The `ext` tactic is temporarily unavailable in Levels 1-7.
You know `ext` from earlier worlds, and it IS the standard tool for
finset equality proofs. But these first levels focus on the membership
characterization lemmas — the building blocks that `ext` proofs are
built from. You need to master `rw [Finset.mem_union]`, `rw [Finset.mem_inter]`,
etc. before combining them via `ext`. The tactic returns in Level 8.

**Your task**: Prove that $3 \\in \\{1, 2\\} \\cup \\{3, 4\\}$.

Since $3$ is in the right-hand set, you'll choose `right` after
rewriting with `mem_union`, then prove $3 \\in \\{3, 4\\}$ using the
insert-peel pattern from Finset Basics.
"

/-- 3 is an element of {1, 2} ∪ {3, 4}. -/
Statement : (3 : ℕ) ∈ ({1, 2} : Finset ℕ) ∪ {3, 4} := by
  Hint "Use `rw [Finset.mem_union]` to convert the union membership
  into a disjunction: is `3` in the left set or the right set?"
  rw [Finset.mem_union]
  Hint "The goal is a disjunction: `3` is in the left set or the right
  set. Since $3$ is in the right set, choose `right`."
  right
  Hint "Now prove membership in the right set. Peel the outer insert with
  `rw [Finset.mem_insert]`."
  rw [Finset.mem_insert]
  Hint (hidden := true) "The goal is `3 = 3 ∨ 3 ∈ singleton 4`.
  Choose `left` and close with `rfl`."
  left
  rfl

Conclusion "
The pattern for union membership:
1. `rw [Finset.mem_union]` — converts `a ∈ s ∪ t` to `a ∈ s ∨ a ∈ t`
2. `left` or `right` — choose which set the element is in
3. Prove membership in that set (using `mem_insert`/`mem_singleton` from Finset Basics)

This is the same rewrite-then-choose pattern you used for `mem_insert`,
but now at the level of entire sets rather than individual elements.

In plain mathematics: to show $x \\in A \\cup B$, either show $x \\in A$ or
$x \\in B$.
"

/-- `Finset.mem_union` states that `a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t`.

## Syntax
```
rw [Finset.mem_union]       -- in the goal
rw [Finset.mem_union] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis involves `x ∈ s ∪ t`. After rewriting,
the goal becomes a disjunction that you handle with `left`/`right`.

## Example
```
-- Goal: 3 ∈ {1, 2} ∪ {3, 4}
rw [Finset.mem_union]
-- Goal: 3 ∈ {1, 2} ∨ 3 ∈ {3, 4}
right
-- Goal: 3 ∈ {3, 4}
```
-/
TheoremDoc Finset.mem_union as "Finset.mem_union" in "Finset"

/-- `Finset.union s t` (written `s ∪ t`) is the finset containing all
elements that belong to `s`, to `t`, or to both.

## Notation
`s ∪ t` — the union of finsets `s` and `t`.

## Key lemma
`Finset.mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t`

## Properties
- Union is commutative: `s ∪ t = t ∪ s`
- Union is associative: `(s ∪ t) ∪ u = s ∪ (t ∪ u)`
- Union with empty: `s ∪ ∅ = s`
- Union is idempotent: `s ∪ s = s`
-/
DefinitionDoc Finset.union as "Finset.union"

TheoremTab "Finset"
NewDefinition Finset.union
NewTheorem Finset.mem_union

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right
