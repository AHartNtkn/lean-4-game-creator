import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 5

Title "Induction on a new property"

Introduction
"
# Induction on a fresh target

Use `Finset.induction_on` to prove a property you have not seen before.

## The statement

For any finset `s` of natural numbers, prove:

```
s.card ≤ s.card + s.card
```

This is arithmetically obvious, but the point is to **practice the
induction pattern** on a fresh target.

## Strategy

Induction on `s`:
- **Base**: `(∅).card ≤ (∅).card + (∅).card` — this is `0 ≤ 0 + 0`.
- **Step**: Given `ih : s'.card ≤ s'.card + s'.card` and `ha : a ∉ s'`,
  use `Finset.card_insert_of_notMem ha` to rewrite, then `omega`.
"

/-- For any finset, `card s ≤ card s + card s`. -/
Statement {α : Type*} [DecidableEq α] (s : Finset α) :
    s.card ≤ s.card + s.card := by
  Hint (hidden := true) "Use `induction s using Finset.induction_on`."
  induction s using Finset.induction_on
  case empty =>
    Hint (hidden := true) "The base case simplifies to `0 ≤ 0`. Use `omega`."
    omega
  case insert a s' ha ih =>
    Hint (hidden := true) "Use `rw [Finset.card_insert_of_notMem ha]` then `omega`."
    rw [Finset.card_insert_of_notMem ha]
    omega

Conclusion
"
You completed a finset induction proof on a fresh statement. The
structure is always the same:

1. Apply `induction s using Finset.induction_on`.
2. Handle the empty base case.
3. In the insert step, use `ha : a ∉ s'` with
   `Finset.card_insert_of_notMem` to manage cardinality, then combine
   with the inductive hypothesis.

**Retrieval check**: This level retrieved finset induction (V4) on
a new property.
"

DisabledTactic trivial decide native_decide aesop simp_all omega
