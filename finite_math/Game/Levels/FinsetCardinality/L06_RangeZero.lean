import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 6

Title "Range 0 is empty"

Introduction
"
# Boundary case: `Finset.range 0`

A common source of confusion: what is `Finset.range 0`?

Since `range n` contains the natural numbers less than `n`, and no
natural number is less than `0`, we get `range 0 = ∅`.

## `Finset.range_zero`

```
Finset.range_zero : Finset.range 0 = ∅
```

This is a boundary case worth internalizing. When you later write
a sum `∑ i in range 0, f i`, it is the empty sum — which equals `0`
for additive types. Knowing that `range 0 = ∅` makes that immediate.

## Your task

Prove two things:
1. `Finset.range 0 = ∅`
2. `(Finset.range 0).card = 0`

The first follows from `range_zero`. The second follows from the first
(by rewriting) plus `card_empty`, or directly from `card_range`.
"

/-- `range 0` is empty and has cardinality 0. -/
Statement : Finset.range 0 = ∅ ∧ (Finset.range 0).card = 0 := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "The first goal is `Finset.range 0 = ∅`. What lemma directly
    states this?"
    Hint (hidden := true) "Use `exact Finset.range_zero`."
    exact Finset.range_zero
  · Hint "The second goal is `(Finset.range 0).card = 0`. You can
    either rewrite with `range_zero` then use `card_empty`, or
    directly use `card_range`."
    Hint (hidden := true) "Use `rw [Finset.card_range]`."
    rw [Finset.card_range]

Conclusion
"
You proved two boundary facts about `range 0`:
- It equals the empty finset.
- Its cardinality is 0.

## Misconception calibration

The key trap is thinking `range n` starts at `1`:
- `range 0 = ∅` — zero elements
- `range 1 = {0}` — one element, and it is `0`
- `range 5 = {0, 1, 2, 3, 4}` — five elements, largest is `4`

This 0-indexing convention matches `Fin n` (whose elements are
`0, ..., n-1`) and is standard in Lean/mathlib.

**In plain language**: \"The set of natural numbers less than 0 is empty.
This is the base case for sums over ranges.\"
"

/-- `Finset.range_zero` states that `Finset.range 0 = ∅`.

No natural number is less than 0, so the range is empty. -/
TheoremDoc Finset.range_zero as "Finset.range_zero" in "Finset"

NewTheorem Finset.range_zero
DisabledTactic trivial decide native_decide aesop simp_all
