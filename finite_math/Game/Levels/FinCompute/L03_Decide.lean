import GameServer.Commands
import Mathlib

World "FinCompute"
Level 3

Title "Introducing decide"

Introduction
"
# The `decide` Tactic

There is an even more powerful automation tactic for finite types: `decide`.

The `decide` tactic works on **decidable propositions** --- statements that
can be checked by a finite computation. Many propositions about `Fin n`
are decidable, because `Fin n` is a finite type with decidable equality.

When `decide` works, it simply *computes* the answer. No case analysis,
no arithmetic reasoning --- just brute-force evaluation.

## When does `decide` work?

`decide` works when:
- The proposition involves only finite types and decidable operations
- The computation terminates in reasonable time
- The type checker can verify the result

For small `Fin n`, this is almost always the case.

## Your task

Prove that `(0 : Fin 3) ≠ (1 : Fin 3)`.

This is a decidable proposition --- we can simply check whether `0` and `1`
are equal in `Fin 3`. They are not, so the proposition is true.

Try just `decide`.
"

/-- 0 and 1 are different elements of `Fin 3`. -/
Statement : (0 : Fin 3) ≠ (1 : Fin 3) := by
  Hint "This is a decidable proposition. Try `decide`."
  decide

/-- `decide` closes goals that are **decidable propositions** --- statements
whose truth value can be computed by a finite algorithm. It works by
evaluating the proposition and checking whether the result is `true`.

**Examples of decidable propositions**:
- Equalities and inequalities between concrete `Fin n` elements
- Boolean combinations (`∧`, `∨`, `¬`) of decidable propositions
- Membership in finite sets (in later worlds)

**When to use**: If your goal involves only concrete values of finite
types and decidable predicates (equality, ordering, membership), try
`decide` first. If it works, you are done.

**Limitation**: `decide` can be slow or fail on large types. For
`Fin 1000`, the computation would be enormous. For small types like
`Fin 3` or `Fin 5`, it is fast and reliable. -/
TacticDoc decide

Conclusion
"
The `decide` tactic is remarkable: it turned a proof obligation into a
computation. There was no reasoning, no strategy --- just evaluation.

Under the hood, `decide` checked:
1. Is `(0 : Fin 3) = (1 : Fin 3)` true or false?
2. It computed: `0.val = 0` and `1.val = 1`, so `0 ≠ 1`.
3. Since the proposition is decidable and evaluates to `true`, the proof is done.

**Decidable propositions will appear again** when you work with finsets ---
membership in a concrete finset is decidable, and filtering requires a
decidable predicate. The word \"decidable\" will become important
vocabulary.

**When to reach for `decide`**: If your goal involves only concrete values
of finite types and decidable predicates (equality, ordering, membership),
try `decide` first.

**Limitation**: `decide` can be slow or fail on large types. For
`Fin 1000`, the computation would be enormous. For small types like
`Fin 3` or `Fin 5`, it is fast and reliable.
"

NewTactic decide
DisabledTactic native_decide
