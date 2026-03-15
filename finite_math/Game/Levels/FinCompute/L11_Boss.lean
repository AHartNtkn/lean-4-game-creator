import GameServer.Commands
import Mathlib

World "FinCompute"
Level 11

Title "Boss: Exhaustive computation on Fin 5"

Introduction
"
# Boss Level: Integrating Everything

Time to combine all the skills from this world.

You will prove a conjunction of two facts:

1. A **numeric computation** with powers: `3 ^ 2 + 4 ^ 2 = 25`
2. A **universal property** about `Fin 5`: for every `i : Fin 5`, `i.val ^ 2 < 25`

## Why this is an integration challenge

The two conjuncts require **different proof strategies**:

- Part 1 is a concrete numeric equality involving powers. Use `norm_num`
  to evaluate it directly.
- Part 2 is a universally quantified property about `Fin 5` involving powers.
  You need `fin_cases` to enumerate all five elements, then `norm_num` to
  evaluate each case.

You will need to:
1. Use `constructor` to split the conjunction
2. Solve part 1 with `norm_num`
3. Solve part 2 with `intro i; fin_cases i <;> norm_num`

There is no new material --- only integration.
"

/-- A conjunction: a numeric computation with powers, and a universal bound on squares in Fin 5. -/
Statement : (3 ^ 2 + 4 ^ 2 = 25) ∧
    (∀ i : Fin 5, i.val ^ 2 < 25) := by
  Hint "The goal is a conjunction `P ∧ Q`. Use `constructor` to split it into
  two subgoals."
  constructor
  Hint "The first goal is a numeric equality involving powers. Use `norm_num` to evaluate it."
  · norm_num
  Hint "The second goal is a universal statement about `Fin 5` involving powers.
  Use `intro i; fin_cases i <;> norm_num`."
  · intro i
    Hint "Now enumerate all elements of `Fin 5` with `fin_cases i`, then
    use `norm_num` to verify each case."
    Hint (hidden := true) "The five cases are:
    - `i = 0`: `0^2 = 0 < 25` ✓
    - `i = 1`: `1^2 = 1 < 25` ✓
    - `i = 2`: `2^2 = 4 < 25` ✓
    - `i = 3`: `3^2 = 9 < 25` ✓
    - `i = 4`: `4^2 = 16 < 25` ✓
    Try `fin_cases i <;> norm_num`."
    fin_cases i <;> norm_num

Conclusion
"
Congratulations on completing the Computing with Fin world!

Your boss proof combined three different skills:
1. **`constructor`** to split a conjunction into parts
2. **`norm_num`** to evaluate a numeric equality with powers
3. **`fin_cases` + `norm_num`** to verify a power inequality for each element

Notice how each part demanded a different approach:
- Part 1 was a pure numeric equality --- `norm_num` evaluated it directly
- Part 2 needed `fin_cases` + `norm_num` (exhaustive case analysis with
  per-case numeric evaluation)

This is the core lesson: **choose the right tool for each subgoal**.

## What you learned in this world

| Tactic | What it does | When to use |
|--------|-------------|-------------|
| `fin_cases` | Splits `i : Fin n` into `n` goals | Exhaustive verification on small `Fin n` |
| `decide` | Evaluates decidable propositions | Concrete equalities/inequalities on finite types |
| `norm_num` | Evaluates numeric expressions | Powers, products, non-linear arithmetic |
| `<;>` | Applies a tactic to all goals | After `fin_cases`, `constructor`, etc. |

**The exhaustive verification pattern:**
```
intro i; fin_cases i <;> closer
```
This pattern checks a property for every element of a small finite type.
It is the Lean equivalent of \"we verify the claim for each element of
the domain\" in paper proofs.

**The tactic selection hierarchy:**
| Situation | Strategy |
|-----------|----------|
| Concrete equality/inequality on small `Fin n` | `decide` (or `norm_num`) |
| Universal property needing per-case computation | `fin_cases <;> norm_num` or `omega` |
| Property following from the bound `i.val < n` alone | `i.isLt` + `omega` |

**Transfer to paper proofs**: The proof you just wrote says:
\"We prove two facts. First, $3^2 + 4^2 = 9 + 16 = 25$ by direct
computation. Second, for each $i \\in \\{0, 1, 2, 3, 4\\}$, we check
$i^2 < 25$: the values are $0, 1, 4, 9, 16$, all less than $25$.\"

In the next worlds, you will work with `Fin 3` as a concrete example
world, and then move beyond `Fin` to study lists, multisets, and
finsets --- the richer finite collections built on the `Fin` foundation.
"

DisabledTactic decide native_decide
