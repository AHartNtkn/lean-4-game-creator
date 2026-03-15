import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 5

Title "Contradiction via cardinality"

Introduction
"
# Empty from cardinality zero

The second proof move connecting cardinality and existence is the
**emptiness-from-card-zero** argument: if a finset has zero elements,
it must be empty.

The key lemma is:
```
Finset.card_eq_zero : s.card = 0 ↔ s = ∅
```

The forward direction (`→`) lets you conclude emptiness from a
cardinality count. This is often used as a **contradiction** move:
if you can show both that `s.card = 0` and that some element belongs
to `s`, you have a contradiction.

## Your task

Given `s.card = 0` and `x ∈ s`, derive `False`.

The strategy is:
1. Use `Finset.card_eq_zero` to rewrite `s.card = 0` into `s = ∅`.
2. Rewrite the membership hypothesis using `s = ∅`.
3. Derive the contradiction: nothing belongs to `∅`.
"

/-- If `s` has zero elements and `x ∈ s`, that is a contradiction. -/
Statement (s : Finset ℕ) (x : ℕ) (hx : x ∈ s) (hcard : s.card = 0) : False := by
  Hint "First, convert `hcard : s.card = 0` into `s = ∅`.
  Use `rw [Finset.card_eq_zero] at hcard` to rewrite the hypothesis
  using the `↔` lemma."
  rw [Finset.card_eq_zero] at hcard
  Hint "Now `hcard : s = ∅`. Rewrite `s` as `∅` in the membership
  hypothesis `hx`. Use `rw [hcard] at hx`."
  Hint (hidden := true) "Use `rw [hcard] at hx`. This changes `hx` from
  `x ∈ s` to `x ∈ ∅`, and since nothing belongs to `∅`, Lean should
  derive the contradiction."
  rw [hcard] at hx
  Hint (hidden := true) "The hypothesis `hx : x ∈ ∅` is now a
  contradiction. Use `exact absurd hx (Finset.notMem_empty x)` to close
  the goal. Or simply `exact Finset.notMem_empty x hx`."
  exact Finset.notMem_empty x hx

Conclusion
"
The proof used a classic **contradiction via cardinality** argument:

1. `Finset.card_eq_zero` converted the cardinality fact into emptiness.
2. Rewriting with `s = ∅` turned `x ∈ s` into `x ∈ ∅`.
3. `Finset.notMem_empty` completed the contradiction.

## The proof pattern

This pattern appears frequently in combinatorics:

> \"We know the set has $k$ elements. But if $k = 0$, then the set is
> empty, contradicting the fact that we found an element in it.\"

The contrapositive is equally useful: if a set contains an element, its
cardinality is positive.

**In plain language**: \"An empty container holds nothing; if we found
something inside, it was not empty.\"
"

/-- `Finset.card_eq_zero` characterizes empty finsets by cardinality:
```
Finset.card_eq_zero : s.card = 0 ↔ s = ∅
```

**When to use**: When you need to derive `s = ∅` from `s.card = 0`, or
vice versa. Often used in contradiction arguments. -/
TheoremDoc Finset.card_eq_zero as "Finset.card_eq_zero" in "Finset"

/-- `Finset.notMem_empty` states that no element belongs to the empty finset:
```
Finset.notMem_empty : ∀ (a : α), a ∉ ∅
```

**When to use**: To derive a contradiction from `x ∈ ∅`. -/
TheoremDoc Finset.notMem_empty as "Finset.notMem_empty" in "Finset"

NewTheorem Finset.card_eq_zero Finset.notMem_empty
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
