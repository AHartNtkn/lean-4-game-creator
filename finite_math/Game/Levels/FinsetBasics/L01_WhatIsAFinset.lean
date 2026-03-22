import Game.Metadata

World "FinsetBasics"
Level 1

Title "What is a Finset?"

Introduction "
# What is a Finset?

A `Finset α` is a finite set of elements from type `α`. Unlike tuples
(`Fin n → α`), finsets are **unordered** and have **no duplicates**.

You can write concrete finsets using literal notation:
- `{1, 2, 3} : Finset ℕ` — a finset of three natural numbers
- `{true, false} : Finset Bool` — a finset of booleans

**Why DecidableEq?** Finsets require `DecidableEq α` — Lean must be
able to decide whether two elements are equal. Why? Because maintaining
'no duplicates' requires checking whether an inserted element is already
present. If you can't decide `a = b`, you can't check for duplicates.
This is why `Finset ℝ` doesn't exist in general — real number equality
isn't decidable.

Under the hood, `{1, 2, 3}` is sugar for nested `insert` calls:
$$\\{1, 2, 3\\} = \\texttt{insert } 1 \\;(\\texttt{insert } 2 \\;\\{3\\})$$

where `{3}` is a *singleton* — a set with exactly one element.

The fundamental question for any set: **is this element a member?**

The key lemma is `Finset.mem_insert`:
$$a \\in \\texttt{insert } b \\; s \\;\\longleftrightarrow\\; a = b \\;\\lor\\; a \\in s$$

In words: `a` is in `insert b s` if either `a = b` (it's the inserted
element) or `a` was already in `s`.

**Your task**: Prove that $1 \\in \\{1, 2, 3\\}$.

Use `rw [Finset.mem_insert]` to unfold the membership test. Since
`{1, 2, 3}` is `insert 1 (insert 2 {3})`, this rewrites the goal to
`1 = 1 ∨ 1 ∈ {2, 3}`. Then choose the left branch with `left` and
close with `rfl`.
"

/-- 1 is an element of the finset {1, 2, 3}. -/
Statement : (1 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) := by
  Hint "Use `rw [Finset.mem_insert]` to convert the membership goal into
  a disjunction: is `1` the inserted element, or is it in the rest?"
  rw [Finset.mem_insert]
  Hint "The goal is now a disjunction: `1 = 1` on the left, or
  `1` is in the remaining set on the right. Since `1 = 1` is true,
  choose the left branch with `left`."
  left
  Hint "The goal is `1 = 1`. Close it with `rfl`."
  rfl

Conclusion "
You just proved set membership by **peeling off** the outermost
`insert` using `Finset.mem_insert`. The pattern:

1. `rw [Finset.mem_insert]` — converts `a ∈ insert b s` to `a = b ∨ a ∈ s`
2. `left` or `right` — choose which branch
3. `rfl` or continue peeling

This is the fundamental membership proof move for finsets.

Since `1` was the *first* element inserted, one peel was enough.
What if the element you're looking for is deeper in the set?
That's the next level.
"

/-- `Finset α` is a finite set of elements from type `α`.

A `Finset` is an unordered collection with no duplicates and
decidable membership.

## Construction
- `{a, b, c} : Finset α` — literal notation (requires `DecidableEq α`)
- `∅ : Finset α` — the empty finset (contains no elements)
- `{a} : Finset α` — a *singleton* finset (exactly one element)
- `insert a s` — add element `a` to finset `s` (no-op if `a ∈ s`)
- `Finset.range n` — the set `{0, 1, ..., n-1}`

## How literal notation works
`{1, 2, 3}` is sugar for `insert 1 (insert 2 {3})`:
- The outermost layer is an `insert`
- Each nested layer is another `insert`
- The innermost `{3}` is a singleton

## Membership
`x ∈ s` is decidable for any `Finset`.

## Key difference from tuples
Tuples (`Fin n → α`) are ordered and accessed by index.
Finsets are unordered and accessed by membership.
-/
DefinitionDoc Finset as "Finset"

/-- `Finset.mem_insert` states that `a ∈ insert b s ↔ a = b ∨ a ∈ s`.

## Syntax
```
rw [Finset.mem_insert]       -- unfold membership in the goal
rw [Finset.mem_insert] at h  -- unfold membership in hypothesis h
```

## When to use it
When the goal or a hypothesis involves `x ∈ insert a s` (which includes
literal finsets like `x ∈ {1, 2, 3}`, since `{1, 2, 3} = insert 1 (insert 2 {3})`).

## Example
```
-- Goal: 1 ∈ {1, 2, 3}
rw [Finset.mem_insert]
-- Goal: 1 = 1 ∨ 1 ∈ {2, 3}
left
rfl
```
-/
TheoremDoc Finset.mem_insert as "Finset.mem_insert" in "Finset"

/-- `Finset.insert a s` adds element `a` to finset `s`.

If `a` is already in `s`, the result is unchanged (no duplicates).

## Notation
`{1, 2, 3}` is sugar for `insert 1 (insert 2 {3})`:
- Each comma corresponds to one `insert`
- The innermost element is a singleton

## Key lemma
`Finset.mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s`

## Idempotency
If `a ∈ s`, then `insert a s = s` (see `Finset.insert_eq_of_mem`).
-/
DefinitionDoc Finset.insert as "Finset.insert"

TheoremTab "Finset"
/-- `Insert.insert a s` is the type class method underlying the `insert` notation.
For finsets, `insert a s` adds element `a` to finset `s`. -/
DefinitionDoc Insert.insert as "Insert.insert"

NewDefinition Finset Finset.insert Insert.insert
NewTheorem Finset.mem_insert

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem
