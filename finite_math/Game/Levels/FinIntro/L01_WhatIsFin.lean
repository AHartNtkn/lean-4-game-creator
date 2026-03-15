import GameServer.Commands
import Mathlib

World "FinIntro"
Level 1

Title "What is Fin n?"

Introduction
"
# Welcome to Finite Index Types

In mathematics, we often need to work with **finite index sets** -- the rows
of a matrix, the terms of a finite sum, the elements of a finite group. In
Lean 4, `Fin n` is the canonical way to represent a set with exactly `n`
elements. It is used everywhere: as the index type for vectors and matrices,
as the domain of finite sums (`Finset.sum`), and as the foundation for
counting arguments. This course will teach you to work with `Fin n` and the
broader finite-mathematics infrastructure built on top of it.

## What is `Fin n`?

`Fin n` is a **subtype** of the natural numbers. An element of `Fin n` is
a pair: a natural number `val`, together with a proof that `val < n`.

In Lean 4, `Fin n` is defined as:
```
structure Fin (n : Nat) where
  mk ::
  val : Nat
  isLt : val < n
```

So `Fin 5` contains the numbers `0, 1, 2, 3, 4` -- each bundled with a proof
that it is less than `5`.

## Your first task

Prove that there exists an element `i` of `Fin 5` whose value is `3`.

To do this, you need to construct a specific element of `Fin 5` and show
its value is `3`. Use `use ⟨3, by omega⟩` to provide the element, then
close the value goal.

The angle-bracket notation `⟨3, proof⟩` is syntactic sugar for the
constructor `Fin.mk 3 proof`. The tactic `omega` can automatically prove
simple arithmetic facts like `3 < 5`.
"

/-- There exists an element of `Fin 5` with value `3`. -/
Statement : ∃ i : Fin 5, i.val = 3 := by
  Hint "Use `use ⟨3, by omega⟩` to provide the element `3 : Fin 5` and close the goal."
  use ⟨3, by omega⟩

Conclusion
"
Excellent! You constructed an element of `Fin 5` -- specifically, the number 3,
bundled with a proof that `3 < 5` -- and showed its value is `3`.

The key idea: `Fin n` is not just a number. It is a number *together with evidence*
that the number is in bounds. This is what makes finite types work in Lean --
the type system itself guarantees that every `Fin n` element is a valid index.

In ordinary mathematics, we would say: \"Let $i$ be a natural number with $i < 5$.\"
In Lean, `i : Fin 5` says exactly the same thing, but the proof obligation is
built into the type.
"

/-- `omega` solves linear arithmetic goals over natural numbers and integers. -/
TacticDoc omega

/-- `exact e` closes the goal if `e` has exactly the right type. -/
TacticDoc exact

/-- `intro h` introduces a hypothesis from the goal. For `P → Q`, it gives you
`h : P` and changes the goal to `Q`. For `¬P` (which is `P → False`), it gives
`h : P` and changes the goal to `False`. -/
TacticDoc intro

/-- `have h := e` or `have h : T := e` introduces a new hypothesis `h` into the
context. This is useful for naming intermediate results in a proof. -/
TacticDoc «have»

/-- `assumption` closes the goal if it matches any hypothesis in the context. -/
TacticDoc assumption

/-- `apply f` reduces the goal by applying `f`. If `f : A → B` and the goal is
`B`, then after `apply f` the goal becomes `A`. -/
TacticDoc apply

/-- `rw [h]` rewrites the goal using the equation `h`. If `h : a = b`, it replaces
`a` with `b` in the goal. Use `rw [← h]` to rewrite in the reverse direction. -/
TacticDoc rw

/-- `constructor` splits a goal with structure `⟨_, _⟩` into separate subgoals.
For `∧` (and) goals, it splits into the left and right conjuncts.
For `↔` (iff) goals, it splits into the forward and backward directions. -/
TacticDoc constructor

/-- `use e` provides a witness for an existential goal `∃ x, P x`. After `use e`,
the goal becomes `P e`. -/
TacticDoc use

/-- `cases h` performs case analysis on `h`. For a disjunction `h : P ∨ Q`, it
creates two goals. For an existential `h : ∃ x, P x`, it gives a witness and
the property. -/
TacticDoc cases

/-- `Fin n` is the type of natural numbers strictly less than `n`. An element
`i : Fin n` consists of a value `i.val : Nat` and a proof `i.isLt : i.val < n`.

`Fin n` has exactly `n` elements: `0, 1, ..., n-1`. -/
DefinitionDoc Fin as "Fin"

/-- `Fin.mk val proof` constructs an element of `Fin n` from a natural number
`val` and a proof that `val < n`. The angle-bracket notation `⟨val, proof⟩`
is shorthand for `Fin.mk val proof`. -/
DefinitionDoc Fin.mk as "Fin.mk"

NewDefinition Fin Fin.mk
NewTactic omega exact intro «have» assumption apply rw constructor use cases
