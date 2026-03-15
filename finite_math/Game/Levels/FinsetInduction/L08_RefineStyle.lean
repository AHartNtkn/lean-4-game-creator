import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 8

Title "Using refine for induction goals"

Introduction
"
# The `refine` approach to induction

So far you have used `induction s using Finset.induction_on` as a tactic.
There is an alternative: use `refine` to apply `Finset.induction_on`
directly, creating placeholders for the base case and inductive step.

## The pattern

```
refine Finset.induction_on s ?_ ?_
```

This applies `Finset.induction_on` to `s` with two placeholders:
- `?_` for the base case (motive for `∅`)
- `?_` for the inductive step

You then fill each placeholder with a focused proof (`·` or `next`).

In the inductive step, the variables are not automatically named —
you must introduce them with `intro a t ha ih`.

## When to use `refine`

The `refine` style is useful when:
- You want to apply a specific induction principle by name
- You are combining induction with other tactics in a `calc` block
- You want fine control over how goals are created

## Your task

Prove that every finset is either empty or has positive cardinality,
using `refine Finset.induction_on s ?_ ?_`.
"

/-- Every finset is either empty or has positive cardinality. -/
Statement (s : Finset Nat) : s = ∅ ∨ 0 < s.card := by
  Hint "Use `refine Finset.induction_on s ?_ ?_` to create two goals:
  one for the empty case and one for the insert case."
  refine Finset.induction_on s ?_ ?_
  · Hint "The base case: `∅ = ∅ ∨ 0 < (∅ : Finset Nat).card`.
    The left disjunct is true."
    Hint (hidden := true) "Use `left` then `rfl`."
    left; rfl
  · Hint "The insert case. Unlike the `induction ... with` syntax,
    the variables are not named yet. Use `intro a t ha ih` to
    introduce them."
    intro a t ha ih
    Hint "Now you have `ha : a ∉ t` and `ih : t = ∅ ∨ 0 < t.card`.
    Take the right disjunct and use `Finset.card_insert_of_notMem ha`."
    Hint (hidden := true) "Use `right`, then
    `rw [Finset.card_insert_of_notMem ha]`, then `omega`."
    right
    rw [Finset.card_insert_of_notMem ha]
    omega

Conclusion
"
You used `refine` to apply `Finset.induction_on` directly.

## Comparing the two styles

**`induction` tactic style:**
```
induction s using Finset.induction_on
case empty => ...
case insert a t ha ih => ...
```

**`refine` application style:**
```
refine Finset.induction_on s ?_ ?_
· ...              -- base case
· intro a t ha ih  -- inductive step
  ...
```

Both produce the same goals. The `induction` style is more common for
straightforward induction proofs. The `refine` style is useful when you
need more control or are building a term proof.

## Ready for the boss

You now have all the tools for the boss level:
- Finset induction (`induction s using Finset.induction_on`)
- Non-membership and cardinality (`card_insert_of_notMem`, `card_insert_le`)
- Subset cardinality (`card_le_card`)
- Nat induction for range properties
- The `have` tactic for intermediate results
- The `refine` alternative

**In plain language**: \"There are two ways to set up a finset induction
proof in Lean: the `induction` tactic (which names variables automatically)
and the `refine` approach (which gives you more control). Both work for
any induction principle.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
DisabledTheorem Finset.eq_empty_or_nonempty Finset.card_pos
