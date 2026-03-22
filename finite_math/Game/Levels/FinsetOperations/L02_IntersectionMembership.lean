import Game.Metadata

World "FinsetOperations"
Level 2

Title "Intersection Membership"

Introduction "
# Intersection: Elements in Both Sets

The **intersection** `s ∩ t` contains only the elements that belong to
*both* `s` and `t`. The membership characterization is:

$$a \\in s \\cap t \\;\\longleftrightarrow\\; a \\in s \\;\\land\\; a \\in t$$

In Lean, this is `Finset.mem_inter`:
```
Finset.mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t
```

The proof move: `rw [Finset.mem_inter]` converts an intersection
membership goal into a conjunction. Then you use `constructor` to split
the conjunction into two goals (membership in `s` and membership in `t`),
and prove each one separately.

**Your task**: Prove that $2 \\in \\{1, 2, 3\\} \\cap \\{2, 4, 6\\}$.
"

/-- 2 is in the intersection of {1, 2, 3} and {2, 4, 6}. -/
Statement : (2 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) ∩ {2, 4, 6} := by
  Hint "Use `rw [Finset.mem_inter]` to convert the intersection
  membership into a conjunction."
  rw [Finset.mem_inter]
  Hint "The goal is a conjunction: `2` is in the left set AND `2` is in
  the right set. Use `constructor` to split it into two goals."
  constructor
  · Hint "Prove membership in the left set. Peel inserts:
    `rw [Finset.mem_insert]`, then `right`,
    then `rw [Finset.mem_insert]`, then `left; rfl`."
    rw [Finset.mem_insert]
    right
    rw [Finset.mem_insert]
    left
    rfl
  · Hint "Prove membership in the right set. Since $2$ is the first
    element, one peel suffices."
    Hint (hidden := true) "`rw [Finset.mem_insert]; left; rfl`."
    rw [Finset.mem_insert]
    left
    rfl

Conclusion "
The pattern for intersection membership:
1. `rw [Finset.mem_inter]` — converts `a ∈ s ∩ t` to `a ∈ s ∧ a ∈ t`
2. `constructor` — splits the conjunction into two subgoals
3. Prove each membership separately

Notice the symmetry with union:
- **Union** produces a disjunction (`∨`) — you choose one side
- **Intersection** produces a conjunction (`∧`) — you prove both sides

In plain mathematics: to show $x \\in A \\cap B$, show $x \\in A$ *and* $x \\in B$.
"

/-- `Finset.mem_inter` states that `a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t`.

## Syntax
```
rw [Finset.mem_inter]       -- in the goal
rw [Finset.mem_inter] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis involves `x ∈ s ∩ t`. After rewriting,
the goal becomes a conjunction that you handle with `constructor`.

## Example
```
-- Goal: 2 ∈ {1, 2, 3} ∩ {2, 4, 6}
rw [Finset.mem_inter]
-- Goal: 2 ∈ {1, 2, 3} ∧ 2 ∈ {2, 4, 6}
constructor
-- Two subgoals: prove each membership
```
-/
TheoremDoc Finset.mem_inter as "Finset.mem_inter" in "Finset"

/-- `Finset.inter s t` (written `s ∩ t`) is the finset containing all
elements that belong to both `s` and `t`.

## Notation
`s ∩ t` — the intersection of finsets `s` and `t`.

## Key lemma
`Finset.mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t`

## Properties
- Intersection is commutative: `s ∩ t = t ∩ s`
- Intersection is associative
- `s ∩ ∅ = ∅`
- `s ∩ s = s`
-/
DefinitionDoc Finset.inter as "Finset.inter"

NewDefinition Finset.inter
NewTheorem Finset.mem_inter

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem
