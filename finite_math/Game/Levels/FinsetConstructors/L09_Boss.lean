import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 9

Title "Boss: Three ways to build a finset"

Introduction
"
# Boss: Building a finset three ways

Time to integrate everything from this world. You will show that three
different construction methods produce the same finset, and compute its
cardinality using structural lemmas.

## The three constructions

1. **Literal notation**: `{1, 2, 3}` -- the curly-brace syntax.
2. **Explicit `insert` chain**: `insert 1 (insert 2 (insert 3 ∅))` --
   the desugared form.
3. **Using `cons`**: `Finset.cons 1 (Finset.cons 2 {3} h₁) h₂` -- with
   explicit non-membership proofs.

## What you must prove

Three things:
1. The literal notation equals the explicit insert chain.
2. A `cons`-built version equals the literal notation.
3. The resulting finset has cardinality 3.

These require:
- Understanding notation desugaring (L03, L04) -- `rfl`
- Using `Finset.cons_eq_insert` to convert `cons` to `insert` (L05)
- Using `Finset.card_insert_of_notMem` to peel insert layers (L08)
- Using `Finset.card_singleton` for the base case (L02)

**Strategy**: Use `constructor` to split conjunctions, `rfl` for
definitional equalities, `rw [Finset.cons_eq_insert]` to convert
`cons` to `insert`, and repeated `rw [Finset.card_insert_of_notMem h]`
followed by `rw [Finset.card_singleton]` for cardinality.

You are given non-membership hypotheses that you will need for the
`cons` equalities and the cardinality computation.
"

/-- Three constructions of `{1, 2, 3}` are equal, and the finset has
3 elements. -/
Statement (h₁ : (2 : Nat) ∉ ({3} : Finset Nat))
    (h₂ : (1 : Nat) ∉ (Finset.cons 2 {3} h₁))
    (h₃ : (1 : Nat) ∉ ({2, 3} : Finset Nat))
    (h₄ : (2 : Nat) ∉ ({3} : Finset Nat)) :
    ({1, 2, 3} : Finset Nat) = insert 1 (insert 2 (insert 3 ∅)) ∧
    Finset.cons 1 (Finset.cons 2 {3} h₁) h₂ = ({1, 2, 3} : Finset Nat) ∧
    ({1, 2, 3} : Finset Nat).card = 3 := by
  Hint "The goal is a three-part conjunction. Split it with `constructor`."
  constructor
  · Hint "The first part asks whether the literal notation equals the
    explicit `insert` chain. The notation desugars to
    `insert 1 (insert 2 (insert 3 ∅))`, so both sides are the same."
    Hint (hidden := true) "Try `rfl`."
    rfl
  · Hint "Split the remaining conjunction with `constructor`."
    constructor
    · Hint "You need to show the `cons`-built finset equals the literal.
      The `cons` calls need to be converted to `insert` calls. What lemma
      bridges `Finset.cons` and `insert`?"
      Hint (hidden := true) "Use `rw [Finset.cons_eq_insert]` to convert
      the outer `cons` to `insert`. Then apply it again for the inner `cons`."
      rw [Finset.cons_eq_insert]
      Hint "One `cons` has been converted to `insert`. There is still an
      inner `cons` remaining. Apply the same rewrite again."
      rw [Finset.cons_eq_insert]
    · Hint "The goal asks for the cardinality of the literal finset to be 3.

      **Strategy**: The notation desugars to `insert 1 (insert 2 (insert 3 ∅))`.
      Use `Finset.card_insert_of_notMem` to peel off each `insert` layer,
      reducing the cardinality to a sum. You have `h₃ : 1 ∉ ...` and
      `h₄ : 2 ∉ ...` available as hypotheses."
      Hint (hidden := true) "Start with `rw [Finset.card_insert_of_notMem h₃]`.
      This peels off the outermost insert."
      rw [Finset.card_insert_of_notMem h₃]
      Hint "Good. Now peel off the next insert layer using `h₄`."
      Hint (hidden := true) "Use `rw [Finset.card_insert_of_notMem h₄]`."
      rw [Finset.card_insert_of_notMem h₄]
      Hint "The finset is now a singleton. What lemma gives its cardinality?"
      Hint (hidden := true) "Use `rw [Finset.card_singleton]`.
      The goal becomes `1 + 1 + 1 = 3`, which closes automatically."
      rw [Finset.card_singleton]

Conclusion
"
Congratulations on completing the Constructing Finsets world!

You proved that three different ways of building `{1, 2, 3}` produce the
same finset, and computed its cardinality step by step. Each construction
method has its uses:

- **Literal notation** `{1, 2, 3}` -- clean and readable
- **Explicit `insert`** `insert 1 (insert 2 {3})` -- shows structure
- **`Finset.cons`** `cons 1 (cons 2 {3} h₁) h₂` -- carries non-membership proofs

## The cardinality computation

The key proof pattern for cardinality was:
1. `rw [Finset.card_insert_of_notMem h]` -- peel off each `insert`, reducing the count
2. `rw [Finset.card_singleton]` -- base case: singletons have cardinality 1
3. The arithmetic `1 + 1 + 1 = 3` closes by `rfl`

This recursive peeling works for any literal finset: `{a, b, c, d}.card`
can be computed by peeling `a`, then `b`, then `c`, then using
`card_singleton` for `{d}`.

## What you learned in this world

- `Finset.empty` / `∅` -- base case of finset construction (L01)
- `Finset.card` / `Finset.card_singleton` -- counting elements (L02)
- `Finset.insert` -- primary construction tool (L03)
- Notation desugaring -- `{a,b,c}` is nested `insert` (L04)
- `Finset.cons` -- `insert` with proof obligation (L05)
- `DecidableEq` -- required for finset operations (L06)
- `Finset` vs `Set` -- different types, different APIs (L07)
- `Finset.card_insert_of_notMem` -- structural cardinality reasoning (L08, Boss)

## Transfer to paper proofs

In ordinary mathematics, we write $\\{1, 2, 3\\}$ without thinking about
*how* the set is built. But in Lean, the construction is explicit: start
from $\\emptyset$, insert 3, insert 2, insert 1. This is useful because it
gives us a recursive structure to reason about -- membership, cardinality,
and subset relations all reduce to questions about `insert`.

The `DecidableEq` requirement has no direct analogue in paper math (we
implicitly assume all sets allow element comparison). But it is an important
computational reality: to build a finite set, you must be able to check
for duplicates.

## What comes next

In the next world, you will learn to **prove membership** in finsets
using `simp` and the `mem_insert` lemma family, and see that `insert`
is idempotent.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
