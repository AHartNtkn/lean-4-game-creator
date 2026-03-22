import Game.Metadata

World "FinsetBasics"
Level 2

Title "Finding Deeper Elements"

Introduction "
# Finding Deeper Elements

In the last level, `1` was the *first* element in `{1, 2, 3}`, so one
`rw [Finset.mem_insert]` plus `left; rfl` was enough.

But what if the element is deeper? To prove `3 ∈ {1, 2, 3}`, you need
to peel past `1` and `2` before finding `3`.

Remember: `{1, 2, 3}` is `insert 1 (insert 2 {3})`. The nesting goes:
- Outermost: `insert 1 (...)`
- Middle: `insert 2 ({3})`
- Innermost: `{3}` (a singleton)

After peeling the first `insert` with `rw [Finset.mem_insert]`,
you get `3 = 1 ∨ 3 ∈ {2, 3}`. Since $3 \\neq 1$, take `right`.

Now the goal is `3 ∈ {2, 3}` — which is `3 ∈ insert 2 {3}`.
Peel again with `rw [Finset.mem_insert]` to get `3 = 2 ∨ 3 ∈ {3}`.
Since $3 \\neq 2$, take `right` again.

Now the goal is `3 ∈ {3}`. This is a **singleton**: the set with
exactly one element. The membership lemma here is
`Finset.mem_singleton`: $a \\in \\{b\\} \\longleftrightarrow a = b$.

Use `rw [Finset.mem_singleton]` to reduce to `3 = 3`, which closes
automatically (since `rw` applies `rfl` when the result is trivially
true).
"

/-- 3 is an element of the finset {1, 2, 3}. -/
Statement : (3 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) := by
  Hint "Peel the outermost insert: `rw [Finset.mem_insert]`."
  rw [Finset.mem_insert]
  Hint "The goal is a disjunction: `3 = 1` or `3` is in the
  remaining set. Since `3 ≠ 1`, choose `right`."
  right
  Hint "Now you need `3` in the smaller set. Peel again:
  `rw [Finset.mem_insert]`."
  rw [Finset.mem_insert]
  Hint "Again a disjunction: `3 = 2` or `3` in the remaining
  singleton. Take `right`."
  right
  Hint "The goal is now membership in a singleton set.
  Use `rw [Finset.mem_singleton]` to reduce to `3 = 3`."
  rw [Finset.mem_singleton]

Conclusion "
The pattern for finding a deeper element:

1. `rw [Finset.mem_insert]` — peel one layer
2. `right` — skip past elements that don't match
3. Repeat until you reach the target
4. At the innermost singleton, `rw [Finset.mem_singleton]` finishes

Notice that `rw [Finset.mem_singleton]` closed the goal without
needing `rfl`. That's because `rw` automatically applies `rfl`
when the rewritten goal is trivially true (`3 = 3`).

In ordinary mathematics, '$3 \\in \\{1, 2, 3\\}$' is obvious. In Lean,
you must show *which* insert it came from. The `mem_insert` /
`mem_singleton` chain is the formal version of 'it's in the list
because I can point to it'.
"

/-- `Finset.mem_singleton` states that `a ∈ {b} ↔ a = b`.

A singleton finset `{b}` contains exactly one element.

## Syntax
```
rw [Finset.mem_singleton]       -- in the goal
rw [Finset.mem_singleton] at h  -- in a hypothesis
```

## When to use it
When you reach the innermost level of a literal finset — the part
that looks like `x ∈ {a}` (a single element in braces).

## Example
```
-- Goal: 3 ∈ {3}
rw [Finset.mem_singleton]
-- closes with rfl (3 = 3)
```

## Warning
`{a}` (singleton) is different from `{a, b}` (which is `insert a {b}`).
Use `mem_singleton` only for true singletons.
-/
TheoremDoc Finset.mem_singleton as "Finset.mem_singleton" in "Finset"

/-- `{a} : Finset α` is the singleton finset containing exactly one element.

## Notation
`{a}` is notation for `Finset.singleton a` (or equivalently `{a} = insert a ∅`).

## Key lemma
`Finset.mem_singleton : x ∈ {a} ↔ x = a`

## When you encounter it
At the innermost layer of literal finsets: `{1, 2, 3}` is
`insert 1 (insert 2 {3})`, and `{3}` is the singleton.
-/
DefinitionDoc Finset.singleton as "Finset.singleton"

NewDefinition Finset.singleton
NewTheorem Finset.mem_singleton

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem
