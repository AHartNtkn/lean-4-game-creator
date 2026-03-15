import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 1

Title "Enumerating all elements of Fin 3"

Introduction
"
# The World of `Fin 3`

Welcome to the world of `Fin 3` --- the type with exactly three elements:
`0`, `1`, and `2`.

In the previous worlds, you learned what `Fin n` is (a natural number
bundled with a proof that it is less than `n`) and how to compute with
it (`fin_cases`, `decide`, `norm_num`). Now we will spend an entire
world working concretely with a single small type, `Fin 3`, to build
your intuition for finite types.

## Why study a specific example?

Abstract understanding of `Fin n` is important, but it is not enough.
By working exhaustively with `Fin 3`, you will develop concrete
intuition: what does a function on a 3-element set look like? What
does injectivity mean when you can check every pair? What goes wrong
when you try to map 3 elements onto 4?

This is the mathematical practice of **concretization**: making
abstract definitions tangible by grounding them in specific, small cases.

## Your task

Prove that every element of `Fin 3` is equal to `0`, `1`, or `2`.

Use `intro i` to pick an arbitrary element, then `fin_cases i` to
split into the three cases. In each case, you need to provide the
correct disjunct. After `fin_cases i`, the goal for the first case
will be `0 = 0 ∨ 0 = 1 ∨ 0 = 2`. Use `left` to choose the first
disjunct, then `rfl`.
"

/-- Every element of `Fin 3` is `0`, `1`, or `2`. -/
Statement : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
  Hint "Start with `intro i` to pick an arbitrary element of `Fin 3`."
  intro i
  Hint "Now use `fin_cases i` to split into three cases --- one for each
  element of `Fin 3`."
  fin_cases i
  · Hint "The goal is `0 = 0 ∨ 0 = 1 ∨ 0 = 2`. Use `left` to select the first
    disjunct `0 = 0`, then close with `rfl`."
    left; rfl
  · Hint "The goal is `1 = 0 ∨ 1 = 1 ∨ 1 = 2`. Use `right; left` to select the
    second disjunct `1 = 1`, then close with `rfl`."
    Hint (hidden := true) "Alternatively: `right` moves past the first disjunct,
    then `left` selects the second one."
    right; left; rfl
  · Hint "The goal is `2 = 0 ∨ 2 = 1 ∨ 2 = 2`. Use `right; right` to reach the
    third disjunct `2 = 2`, then close with `rfl`."
    right; right; rfl

/-- `left` selects the left side of a disjunction goal `P ∨ Q`, changing the
goal to `P`. Similarly, `right` selects the right side, changing the goal to `Q`.

**Example**: If the goal is `a = 0 ∨ a = 1`, then `left` changes the goal to `a = 0`.

**When to use**: When you know which disjunct is true and want to prove just that one. -/
TacticDoc left

/-- `right` selects the right side of a disjunction goal `P ∨ Q`, changing the
goal to `Q`. Similarly, `left` selects the left side, changing the goal to `P`.

**Example**: If the goal is `a = 0 ∨ a = 1`, then `right` changes the goal to `a = 1`.

**When to use**: When you know which disjunct is true and want to prove just that one. -/
TacticDoc right

/-- `Fintype.card α` returns the number of elements of a type `α` that Lean knows
is finite (i.e., has a `Fintype` instance).

For `Fin n`, `Fintype.card (Fin n) = n`. For `Bool`, `Fintype.card Bool = 2`.

**When to use**: When you need to reason about how many elements a finite type has. -/
DefinitionDoc Fintype.card as "Fintype.card"

/-- `trivial` attempts to close a goal using simple methods including
`assumption`, `rfl`, and `Decidable` evaluation. On small finite types,
it can solve goals automatically without showing any proof steps.

In this course, `trivial` is disabled so that you practice the manual
proof patterns. -/
TacticDoc trivial

NewTactic left right
NewDefinition Fintype.card
DisabledTactic trivial decide native_decide omega simp aesop simp_all

Conclusion
"
Every element of `Fin 3` is `0`, `1`, or `2`. There are no other possibilities.

Notice the proof shape: `fin_cases i` split the single universal goal into
three concrete cases, and in each case you chose the correct disjunct with
`left`/`right` and closed with `rfl`. This is the **exhaustive enumeration**
pattern applied to a disjunction.

**Proof move retrieval**: You used `fin_cases` from the Computing with Fin world.
But instead of closing each case with `omega` or `norm_num`, you had to navigate
a disjunction --- a different kind of work on the same structural foundation.

**In plain language**: \"The set $\\{0, 1, 2\\}$ consists of exactly the elements
$0$, $1$, and $2$. We verify this by checking each element individually.\"
"
