import Game.Metadata

World "FinsetOperations"
Level 4

Title "Filter by Predicate"

Introduction "
# Filter: Selecting Elements by a Property

`s.filter p` keeps only the elements of `s` that satisfy predicate `p`.
The membership characterization is:

$$a \\in s.\\text{filter } p \\;\\longleftrightarrow\\; a \\in s \\;\\land\\; p(a)$$

In Lean, this is `Finset.mem_filter`:
```
Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a
```

**Why filter, when we already have intersection?** Intersection `s ∩ t`
selects elements that belong to *another set*. Filter `s.filter p`
selects elements that satisfy a *predicate* — a property like 'is even'
or 'is less than 10'. These are different interfaces to the same idea
of restricting membership: intersection uses a set, filter uses a
condition. In fact, `s.filter (fun x => x ∈ t)` is exactly `s ∩ t`.
Filter is the more general operation — you can filter by any decidable
property, not just membership in another set.

The proof move: `rw [Finset.mem_filter]` converts a filter membership
goal into a conjunction. The first part is membership in the original
set, and the second part is that the predicate holds.

**Your task**: Prove that $4 \\in \\text{range}(6).\\text{filter}(n \\mapsto n \\% 2 = 0)$.

In words: 4 is in the set of even numbers less than 6.
"

/-- 4 is in the set of even numbers in range 6. -/
Statement : (4 : ℕ) ∈ (Finset.range 6).filter (fun n => n % 2 = 0) := by
  Hint "Use `rw [Finset.mem_filter]` to split the filter membership
  into two parts: membership in the range, and the predicate."
  rw [Finset.mem_filter]
  Hint "The goal is `4 ∈ Finset.range 6 ∧ 4 % 2 = 0`. Use
  `constructor` to split it."
  constructor
  · Hint "Prove `4 ∈ Finset.range 6`. Recall from Finset Basics:
    `rw [Finset.mem_range]` converts this to `4 < 6`, then `omega`."
    rw [Finset.mem_range]
    omega
  · Hint "Prove `4 % 2 = 0`. This is a concrete computation —
    `rfl` handles it since `4 % 2` computes to `0`."
    rfl

Conclusion "
The pattern for filter membership:
1. `rw [Finset.mem_filter]` — converts `a ∈ s.filter p` to `a ∈ s ∧ p a`
2. `constructor` — split the conjunction
3. Prove membership in `s` (the container)
4. Prove that `p a` holds (the predicate)

Notice the similarity to `mem_sdiff`: both produce conjunctions. The
difference is in the second component:
- **sdiff**: `a ∉ t` (non-membership)
- **filter**: `p a` (predicate holds)

For concrete predicates like `n % 2 = 0`, the predicate goal often
reduces by computation and `rfl` closes it. For more complex predicates,
you may need `omega` or other tactics.

In plain mathematics: $x \\in \\{a \\in S \\mid P(a)\\}$ means $x \\in S$
and $P(x)$.

**Connection to set difference**: Filtering by a negated predicate
is closely related to set difference. If you think of `s.filter (fun x => x ∉ t)`
as 'elements of `s` not in `t`,' that's exactly `s \\\\ t`. This
connection will deepen when you study complement reasoning later.

**Connection to intersection**: Filter with a membership predicate
*is* intersection: `s.filter (fun x => x ∈ t) = s ∩ t`. This follows
directly from `mem_filter` and `mem_inter` — both say
'in `s` AND satisfies a condition.' Intersection is just the special
case where the condition is membership in another set.
"

/-- `Finset.mem_filter` states that `a ∈ s.filter p ↔ a ∈ s ∧ p a`.

## Syntax
```
rw [Finset.mem_filter]       -- in the goal
rw [Finset.mem_filter] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis involves `x ∈ s.filter p`. After
rewriting, the goal becomes a conjunction: `x ∈ s` and `p x`.

## Example
```
-- Goal: 4 ∈ (Finset.range 6).filter (fun n => n % 2 = 0)
rw [Finset.mem_filter]
-- Goal: 4 ∈ Finset.range 6 ∧ 4 % 2 = 0
```
-/
TheoremDoc Finset.mem_filter as "Finset.mem_filter" in "Finset"

/-- `Finset.filter p s` keeps only the elements of `s` that satisfy
predicate `p`.

## Syntax
```
s.filter p           -- dot notation
Finset.filter p s    -- explicit
```

## Key lemma
`Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a`

## Requirements
The predicate `p` must be decidable (`DecidablePred p`).
For predicates involving `<`, `>`, `=`, `%` on natural numbers,
this is automatic.

## Example
```
(Finset.range 10).filter (fun n => n % 2 = 0)
-- = {0, 2, 4, 6, 8}
```
-/
DefinitionDoc Finset.filter as "Finset.filter"

NewDefinition Finset.filter
NewTheorem Finset.mem_filter

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_filter
