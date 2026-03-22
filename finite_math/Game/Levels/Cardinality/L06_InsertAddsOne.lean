import Game.Metadata

World "Cardinality"
Level 6

Title "Insert Adds One"

Introduction "
# Inserting a New Element

If `a` is **not** already in `s`, then inserting `a` increases the
cardinality by exactly one:

$a \\notin s \\implies |\\text{insert}(a, s)| = |s| + 1$

In Lean:
```
Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1
```

The hypothesis `a ∉ s` is essential. If `a` were already in `s`, then
`insert a s = s` (by the idempotency you saw in FinsetBasics), and
the cardinality wouldn't change. The theorem requires you to *prove*
the element is new before it promises the count goes up.

**Your task**: Given that `a ∉ s`, prove that inserting `a` increases
the cardinality by 1.
"

/-- Inserting a new element increases cardinality by 1. -/
Statement (s : Finset ℕ) (a : ℕ) (h : a ∉ s) :
    (insert a s).card = s.card + 1 := by
  Hint "You have `h : a ∉ s` and need to show `(insert a s).card = s.card + 1`.
  This is exactly `Finset.card_insert_of_notMem h`."
  Hint (hidden := true) "Try `exact Finset.card_insert_of_notMem h`."
  exact Finset.card_insert_of_notMem h

Conclusion "
`Finset.card_insert_of_notMem` is the inductive step for cardinality.
Combined with the base cases (`card_empty`, `card_singleton`), it lets
you compute the cardinality of any finset built by iterated insertion:

$$|\\emptyset| = 0, \\quad |\\{a\\}| = 1, \\quad |\\text{insert}(a, s)| = |s| + 1 \\text{ (if } a \\notin s\\text{)}$$

The non-membership hypothesis is the critical ingredient — without it,
the lemma doesn't apply. The next level puts this to work: computing
the cardinality of a concrete finset by chaining `card_insert` steps.
"

/-- `Finset.card_insert_of_notMem h` states that when `h : a ∉ s`,
`(insert a s).card = s.card + 1`.

## Syntax
```
exact Finset.card_insert_of_notMem h
rw [Finset.card_insert_of_notMem h]
```

## When to use it
When the goal involves the cardinality of `insert a s` and you know
(or can prove) that `a ∉ s`.

## Important
The hypothesis `a ∉ s` is required. If `a ∈ s`, then `insert a s = s`
and the cardinality does not change.

## Example
```
-- h : 5 ∉ s
-- Goal: (insert 5 s).card = s.card + 1
exact Finset.card_insert_of_notMem h
```
-/
TheoremDoc Finset.card_insert_of_notMem as "Finset.card_insert_of_notMem" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_insert_of_notMem

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
