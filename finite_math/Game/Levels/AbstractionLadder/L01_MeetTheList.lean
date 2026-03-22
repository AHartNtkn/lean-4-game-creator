import Game.Metadata

World "AbstractionLadder"
Level 1

Title "Meet the List"

Introduction "
# The Abstraction Ladder: List → Multiset → Finset

You've been working with `Finset` — finite sets with no duplicates and no
ordering. But where do finsets come from? What's underneath?

The answer is a **three-layer abstraction**:

| Layer | Type | Ordered? | Duplicates? |
|---|---|---|---|
| Bottom | `List α` | yes | yes |
| Middle | `Multiset α` | no | yes |
| Top | `Finset α` | no | no |

Each layer *forgets* something:
- `List → Multiset` forgets **order** (by quotienting by permutations)
- `Multiset → Finset` forgets **duplicates** (by deduplication)

**Why does Mathlib need all three layers?** Consider two scenarios:
- **Shopping cart**: You buy 2 apples and 1 banana. The *order* you
  added items doesn't matter, but the *quantities* do. You need a
  **multiset**: `{apple, apple, banana}`.
- **Ingredient list**: A recipe calls for apples and bananas. You
  don't care *how many* of each — just *which* ingredients appear.
  You need a **finset**: `{apple, banana}`.

Lists alone can't express 'order doesn't matter.' Finsets alone
can't track quantities. Each layer solves a different problem, and
the conversions between them let you move to whichever level has
the right tools for your current proof.

This world climbs the ladder from the bottom. We start with lists.

A `List α` is exactly what you'd expect: an ordered sequence of elements.
You write them with square brackets: `[1, 2, 3]`.

Under the hood, a list is built from two constructors:
- `[]` — the empty list
- `a :: l` — `a` prepended to list `l` ('cons')

So `[1, 2, 3]` is sugar for `1 :: 2 :: 3 :: []`.

The length of a list counts its elements:
- `List.length_nil : [].length = 0`
- `List.length_cons : (a :: l).length = l.length + 1`

**Your task**: Given a list `l` of known length, determine the length
of `a :: l`.
"

/-- Prepending an element to a list increases its length by 1. -/
Statement (a : ℕ) (l : List ℕ) (h : l.length = 3) : (a :: l).length = 4 := by
  Hint "The goal involves `(a :: l).length`. Use `List.length_cons` to
  rewrite this as `l.length + 1`."
  rw [List.length_cons]
  Hint "The goal is now `l.length + 1 = 4`. Use the hypothesis `h` to
  substitute `l.length` with `3`."
  Hint (hidden := true) "Try `rw [h]`."
  rw [h]

Conclusion "
`List.length_cons` is one of the two base facts about list length (the
other being `List.length_nil : [].length = 0`). Together they define
length by recursion on the list structure.

In plain math: if a sequence has $n$ elements, prepending one gives
$n + 1$ elements.

**Reusable recipe**: When you see a goal about `(a :: l).length`,
reach for `List.length_cons`.
"

/-- `List.length_cons` states that `(a :: l).length = l.length + 1`.

## Syntax
```
exact List.length_cons
rw [List.length_cons]
```

## When to use it
When the goal involves the length of a cons'd list `(a :: l).length`.
-/
TheoremDoc List.length_cons as "List.length_cons" in "List"

/-- `List.length_nil` states that `[].length = 0`.

## Syntax
```
exact List.length_nil
rw [List.length_nil]
```

## When to use it
When the goal involves the length of the empty list.
-/
TheoremDoc List.length_nil as "List.length_nil" in "List"

/-- `List` is an ordered sequence of elements built from `[]` (empty)
and `a :: l` (cons). Lists can contain duplicates and order matters.

## Notation
```
[1, 2, 3]    -- sugar for 1 :: 2 :: 3 :: []
a :: l       -- prepend a to list l
```
-/
DefinitionDoc List as "List"

/-- `List.length` returns the number of elements in a list.

## Key lemmas
- `List.length_nil : [].length = 0`
- `List.length_cons : (a :: l).length = l.length + 1`
- `List.length_append : (l₁ ++ l₂).length = l₁.length + l₂.length`
-/
DefinitionDoc List.length as "List.length"

TheoremTab "List"
NewDefinition List List.length
NewTheorem List.length_cons List.length_nil

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
