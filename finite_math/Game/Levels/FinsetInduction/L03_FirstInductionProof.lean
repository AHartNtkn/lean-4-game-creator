import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 3

Title "First finset induction proof"

Introduction
"
# Using the inductive hypothesis

In the previous level, you did not need the inductive hypothesis `ih`.
This time you will.

## The key insight

In finset induction, the inductive step gives you:
- `a : α` — the element being inserted
- `s' : Finset α` — the smaller finset
- `ha : a ∉ s'` — non-membership proof
- `ih` — the inductive hypothesis: the property holds for `s'`

When the property involves cardinality, you typically:
1. Use `Finset.card_insert_of_notMem ha` to rewrite `(insert a s').card`
   as `s'.card + 1`.
2. Use `ih` to handle the `s'.card` part.
3. Close the arithmetic with `omega`.

## Your task

Prove that `s.card = 0 → s = ∅` by finset induction.

- **Base case**: `(∅).card = 0 → ∅ = ∅` — trivially `rfl`.
- **Inductive step**: `(insert a s').card = 0 → insert a s' = ∅`.
  Use `ha : a ∉ s'` to rewrite the card, getting `s'.card + 1 = 0`.
  This is a contradiction (a natural number plus 1 is never 0).
"

/-- If a finset has cardinality 0, it must be empty. -/
Statement {α : Type*} [DecidableEq α] (s : Finset α)
    (h : s.card = 0) : s = ∅ := by
  Hint "Start with `induction s using Finset.induction_on`."
  induction s using Finset.induction_on
  case empty =>
    Hint "The base case: `∅ = ∅`. This is `rfl`."
    rfl
  case insert a s' ha ih =>
    Hint "You have `h : (insert a s').card = 0` and `ha : a ∉ s'`.
    Use `rw [Finset.card_insert_of_notMem ha] at h` to rewrite `h` to
    `s'.card + 1 = 0`. This is impossible for natural numbers."
    Hint (hidden := true) "After `rw [Finset.card_insert_of_notMem ha] at h`,
    the hypothesis `h : s'.card + 1 = 0` is a contradiction.
    Use `omega` to close it."
    rw [Finset.card_insert_of_notMem ha] at h
    omega

Conclusion
"
You proved that `card s = 0` implies `s = ∅` by finset induction.

## The pattern: contradiction in the insert case

Notice what happened in the inductive step:
1. You had `h : (insert a s').card = 0`.
2. Using `ha : a ∉ s'`, you rewrote the card to `s'.card + 1`.
3. The hypothesis `s'.card + 1 = 0` is impossible (natural numbers
   cannot be negative), so `omega` closed the goal.

This is a common pattern: the insert case leads to a **contradiction**
when the property is incompatible with having elements. The
non-membership hypothesis `ha` is essential — without it, you cannot
rewrite `card (insert a s')`.

## Note

The mathlib lemma `Finset.card_eq_zero` states this as an iff:
`s.card = 0 ↔ s = ∅`. We disabled it so you could practice the
induction pattern. In future proofs, you may use it directly.

**In plain language**: \"If a set has zero elements, it must be empty.
We prove this by considering how finsets are built: the empty set has
zero elements (trivially), and any set formed by inserting an element
has at least one element (contradicting the hypothesis).\"
"

DisabledTactic trivial decide native_decide aesop simp_all
DisabledTheorem Finset.card_eq_zero
