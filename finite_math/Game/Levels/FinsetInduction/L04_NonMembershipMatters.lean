import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 4

Title "Why a ∉ s matters"

Introduction
"
# The non-membership hypothesis

In finset induction, the insert case gives you `ha : a ∉ s`. This
hypothesis is more than a technicality — it is what makes the induction
work. Without it, you could not control the cardinality change from
`s` to `insert a s`.

## Recall

- `Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1`
- `Finset.card_insert_of_mem : a ∈ s → (insert a s).card = s.card`

When `a ∉ s`, inserting `a` adds exactly one element. When `a ∈ s`,
inserting `a` is a no-op. The non-membership hypothesis `ha` in the
induction step guarantees we are in the first case.

## Your task

Prove that if a finset is nonempty, its cardinality is positive.

- **Base case**: `∅.Nonempty` is false, so the implication is vacuously
  true. Use `exact absurd h Finset.not_nonempty_empty` to derive a
  contradiction.
- **Inductive step**: `(insert a s').Nonempty → 0 < (insert a s').card`.
  Use `ha : a ∉ s'` to rewrite the cardinality, then `omega`.
"

/-- A nonempty finset has positive cardinality. -/
Statement {α : Type*} [DecidableEq α] (s : Finset α)
    (h : s.Nonempty) : 0 < s.card := by
  Hint "Start with `induction s using Finset.induction_on`."
  induction s using Finset.induction_on
  case empty =>
    Hint "The base case: prove `0 < (∅ : Finset α).card` assuming
    `h : (∅ : Finset α).Nonempty`. But the empty finset is not nonempty!
    Use `exact absurd h Finset.not_nonempty_empty` to derive a contradiction."
    Hint (hidden := true) "Use `exact absurd h Finset.not_nonempty_empty`."
    exact absurd h Finset.not_nonempty_empty
  case insert a s' ha ih =>
    Hint "You have `ha : a ∉ s'` and need `0 < (insert a s').card`.
    Rewrite the cardinality using `rw [Finset.card_insert_of_notMem ha]`."
    Hint (hidden := true) "After `rw [Finset.card_insert_of_notMem ha]`,
    the goal becomes `0 < s'.card + 1`. Use `omega`."
    rw [Finset.card_insert_of_notMem ha]
    omega

Conclusion
"
You proved that nonempty finsets have positive cardinality — and the
non-membership hypothesis `ha` was essential for the cardinality rewrite.

## Two patterns in finset induction

You have now seen two common patterns in the base case:

1. **Direct proof** (L02, L03): The base case is straightforwardly true.
   Example: `∅ = ∅` is `rfl`.

2. **Vacuous truth** (this level): The base case hypothesis is false
   for `∅`, so the implication is vacuously true. Example:
   `∅.Nonempty` is false, so `∅.Nonempty → ...` holds trivially.

Both are valid and common. Recognizing which pattern applies is part
of setting up a finset induction proof.

## The role of `ha : a ∉ s`

In the inductive step, `ha` lets you:
- Rewrite `(insert a s').card` as `s'.card + 1` (the count increases)
- Know that `a` is genuinely new (not a duplicate)

Without `ha`, `insert a s'` might not change the cardinality at all,
and the induction would not make progress.

**In plain language**: \"A nonempty set has at least one element, so its
count is positive. The finset induction proof works because inserting a
genuinely new element always increases the count by one.\"
"

/-- `Finset.not_nonempty_empty` states that `¬ (∅ : Finset α).Nonempty`.

The empty finset is not nonempty. Use this with `absurd` to handle
vacuous base cases. -/
TheoremDoc Finset.not_nonempty_empty as "Finset.not_nonempty_empty" in "Finset"

NewTheorem Finset.not_nonempty_empty
DisabledTactic trivial decide native_decide aesop simp_all
DisabledTheorem Finset.Nonempty.card_pos Finset.card_pos
