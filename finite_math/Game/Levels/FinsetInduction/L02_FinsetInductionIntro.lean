import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 2

Title "Introducing Finset.induction_on"

Introduction
"
# A new induction principle

Every finset is either:
- the empty finset `∅`, or
- obtained by **inserting** an element `a` into a smaller finset `s`,
  where `a ∉ s`.

This gives us an induction principle:

```
Finset.induction_on :
  motive ∅ →
  (∀ a s, a ∉ s → motive s → motive (insert a s)) →
  motive s
```

To prove a property of all finsets, you show:
1. **Base case** (`empty`): the property holds for `∅`.
2. **Inductive step** (`insert`): if the property holds for `s`, and
   `a ∉ s`, then it holds for `insert a s`.

## The syntax

```
induction s using Finset.induction_on
case empty => ...
case insert a s' ha ih => ...
```

Here:
- `a` is the element being inserted
- `s'` is the smaller finset
- `ha : a ∉ s'` is the non-membership hypothesis
- `ih` is the inductive hypothesis (the property holds for `s'`)

## Your task

Prove that every finset is either empty or nonempty. Use
`induction s using Finset.induction_on` to split into two cases.
"

/-- Every finset is either empty or nonempty. -/
Statement {α : Type*} [DecidableEq α] (s : Finset α) :
    s = ∅ ∨ s.Nonempty := by
  Hint "Use `induction s using Finset.induction_on` to split into the
  empty and insert cases."
  induction s using Finset.induction_on
  case empty =>
    Hint "The base case: prove `∅ = ∅ ∨ (∅ : Finset α).Nonempty`.
    The left disjunct is true by `rfl`."
    Hint (hidden := true) "Use `left` then `rfl`."
    left; rfl
  case insert a s' ha ih =>
    Hint "The insert case: prove `insert a s' = ∅ ∨ (insert a s').Nonempty`.
    Since `insert a s'` is clearly nonempty, take the right disjunct."
    Hint (hidden := true) "Use `right` then `exact Finset.insert_nonempty a s'`."
    right
    exact Finset.insert_nonempty a s'

Conclusion
"
You completed your first `Finset.induction_on` proof!

## What happened

The tactic `induction s using Finset.induction_on` replaced the single
goal about an arbitrary finset `s` with two goals:

1. `empty`: prove the property for `∅`
2. `insert`: given `a`, `s'`, `ha : a ∉ s'`, and `ih` (the property
   for `s'`), prove the property for `insert a s'`

Notice that in this proof, we did not even need `ih` — the insert case
was easy enough without it. In harder proofs, the inductive hypothesis
will be essential.

## Comparing with Nat induction

| | Nat induction | Finset induction |
|---|---|---|
| Base | `zero` (`0`) | `empty` (`∅`) |
| Step | `succ n` (`n + 1`) | `insert a s` |
| Hypothesis | `ih : P n` | `ih : P s` |
| Extra | — | `ha : a ∉ s` |

The extra hypothesis `a ∉ s` is what makes finset induction unique:
when you build a finset by inserting, the new element must not already
be present (otherwise `insert` is a no-op).

**In plain language**: \"Every finset is built from the empty set by
inserting elements one at a time. To prove something about all finsets,
prove it for the empty set and show it is preserved by insertion.\"
"

/-- `Finset.insert_nonempty a s` proves that `insert a s` is nonempty.

A finset with at least one inserted element is never empty. -/
TheoremDoc Finset.insert_nonempty as "Finset.insert_nonempty" in "Finset"

NewTheorem Finset.insert_nonempty
DisabledTactic trivial decide native_decide aesop simp_all
DisabledTheorem Finset.eq_empty_or_nonempty
