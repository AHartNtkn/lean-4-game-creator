import GameServer.Commands
import Mathlib

World "Capstone"
Level 8

Title "Transfer: the finite-math toolkit"

Introduction
"
# Transfer: Describe the toolkit

This is a **transfer** level. The goal is mathematically trivial — the
real exercise is reflection.

## What you have learned

Over this course, you have internalized a large toolkit:

| Area | What you can do |
|------|----------------|
| **Finite types** | Construct and reason about `Fin n`; use `fin_cases` for exhaustion |
| **Finsets** | Build, combine, filter, and transform finite sets; prove membership |
| **Cardinality** | Count elements of types and sets; use `card_prod`, `card_sum`, `card_fin` |
| **Pigeonhole** | Derive collisions from cardinality inequalities |
| **Big operators** | Sum and multiply over finite sets; split, reindex, and estimate |
| **Induction** | Prove sum identities by induction on `range` or `Finset.induction` |
| **Combinatorics** | Factorials, binomial coefficients, Pascal's rule, binomial theorem |
| **Finsupp** | Finitely supported functions, their sums and support |
| **Matrices** | Matrices as functions over finite types; diagonal, transpose, multiplication |

## Your task

Prove the trivial identity `Fintype.card (Fin 1) = 1`.

While you do this, think about the transfer question: **If someone
gave you a problem about finite sets, finite sums, or counting — what
tools would you reach for first?** The answer to that question is the
real deliverable of this course.
"

/-- `Fintype.card (Fin 1) = 1` — a trivial fact to anchor reflection. -/
Statement : Fintype.card (Fin 1) = 1 := by
  Hint "Use `exact Fintype.card_fin 1` to close this directly.

  The real exercise is not the proof — it is the reflection in the
  introduction above."
  Hint (hidden := true) "Try `exact Fintype.card_fin 1`."
  exact Fintype.card_fin 1

Conclusion
"
## The transfer moment

The proof was one line. The value is in the reflection.

If someone asks you to prove a fact about finite objects, your mental
checklist should now include:

1. **What type represents the finite set?** (`Fin n`, `Finset α`, `Fintype α`)
2. **Is this a counting problem?** (`Fintype.card`, `Finset.card`, pigeonhole)
3. **Is this a summation/product problem?** (`Finset.sum`, `Finset.prod`)
4. **Does it involve subsets?** (`powerset`, `filter`, membership)
5. **Does it involve matrices or linear algebra?** (`Matrix`, `trace`, `mul_apply`)
6. **Is there an inductive structure?** (`sum_range_succ`, `Finset.induction`)
7. **Is there a combinatorial identity?** (binomial coefficients, Pascal's rule)

This checklist works in Lean. It also works on paper.

## What separates a good prover from a great one

A good prover knows the lemmas. A great prover knows *when to reach for
each one*. This course has given you both the lemmas and the practice of
choosing among them.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
