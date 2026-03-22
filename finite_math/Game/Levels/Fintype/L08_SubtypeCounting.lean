import Game.Metadata

World "Fintype"
Level 8

Title "Subtype Counting"

Introduction "
# Subtypes of Finite Types

You've been using `Fin n` since the first world. But what IS `Fin n`?
It's a **subtype**: `Fin n = { i : ℕ // i < n }` — the natural numbers
less than `n`. Even though `ℕ` is infinite, the predicate `i < n` picks
out only finitely many values.

More generally, `{ x : α // P x }` picks out the elements of `α`
satisfying the predicate `P`. When `α` is finite, any subtype is
automatically finite too — Lean synthesizes the `Fintype` instance
without you having to construct it.

The composition rules you've learned (products multiply, sums add,
functions exponentiate) have a companion for subtypes:

$$|\\{x : \\alpha \\mid \\neg P\\,x\\}| = |\\alpha| - |\\{x : \\alpha \\mid P\\,x\\}|$$

The theorem `Fintype.card_subtype_compl` captures this: the count of
elements NOT satisfying `P` equals the total minus those satisfying `P`.

**Your task**: Given that `α` has 10 elements and 3 satisfy `P`,
prove that 7 do not.
"

/-- If α has 10 elements and 3 satisfy P, then 7 do not. -/
Statement (α : Type*) [Fintype α] (P : α → Prop) [DecidablePred P]
    [Fintype { x // P x }] [Fintype { x // ¬P x }]
    (hα : Fintype.card α = 10) (hp : Fintype.card { x // P x } = 3) :
    Fintype.card { x // ¬P x } = 7 := by
  Hint "Use `rw [Fintype.card_subtype_compl]` to apply the complement
  counting formula. This rewrites `card negP` into `card α - card P`."
  Hint (hidden := true) "Try `rw [Fintype.card_subtype_compl, hα, hp]`."
  rw [Fintype.card_subtype_compl, hα, hp]

Conclusion "
Subtypes are the fourth composition rule:

| Construction | Formula | Name |
|---|---|---|
| `α × β` | `card α * card β` | Multiplication |
| `α ⊕ β` | `card α + card β` | Addition |
| `α → β` | `card β ^ card α` | Exponentiation |
| `{ x // ¬P x }` | `card α - card P` | Complement |

The complement formula is the type-level version of the complement
counting you learned in the Cardinality world. The same mathematical
idea, now working on entire types instead of finsets.

**Warning about ℕ subtraction**: The formula `card α - card P` uses
natural number subtraction, which floors at zero. If `card P > card α`
(which can't happen for subtypes, since `P` picks out elements of `α`),
the result would silently be 0 rather than negative. In formalized
mathematics, this is a common source of bugs. The additive form
`card {x // ¬P x} + card {x // P x} = card α` avoids this issue
entirely. Keep this in mind when you encounter ℕ subtraction in later
worlds.

Fun fact: `Fin n` is itself a subtype `{ i : ℕ // i < n }`.
Every time you wrote `Fintype.card (Fin n) = n`, you were using a
result about subtype cardinality under the hood.

Next: practice combining subtype counting with products.
"

/-- `Fintype.card_subtype_compl` states that
`Fintype.card { x // ¬P x } = Fintype.card α - Fintype.card { x // P x }`.

The cardinality of the complement subtype equals the total cardinality
minus the cardinality of the subtype.

## Syntax
```
rw [Fintype.card_subtype_compl]    -- rewrites card {x // ¬P x}
```

## When to use it
When the goal contains `Fintype.card { x // ¬P x }` and you want to
decompose it using complement counting.

## Connection to Finset complement counting
This is the type-level analogue of `Finset.card_sdiff_add_card_inter`.
-/
TheoremDoc Fintype.card_subtype_compl as "Fintype.card_subtype_compl" in "Fintype"

NewTheorem Fintype.card_subtype_compl

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
