import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 4

Title "sum_cons"

Introduction
"
# Decomposing a sum with `cons`

Recall from the Finset Induction world that `Finset.cons a s h` builds
a new finset by prepending `a` to `s`, given a proof `h : a ∉ s`. The
sum lemma for `cons` says:

```
Finset.sum_cons (h : a ∉ s) :
  ∑ x ∈ Finset.cons a s h, f x = f a + ∑ x ∈ s, f x
```

This is the additive analogue of peeling off the first element.

## Your task

Given an arbitrary finset `s : Finset Nat`, an element `a : Nat`
with `ha : a ∉ s`, prove:

```
∑ x ∈ Finset.cons a s ha, (x * 2) = a * 2 + ∑ x ∈ s, (x * 2)
```

This is a direct application of `Finset.sum_cons`.
"

/-- Decomposing a sum via `cons`. -/
Statement (s : Finset Nat) (a : Nat) (ha : a ∉ s) :
    ∑ x ∈ Finset.cons a s ha, (x * 2) = a * 2 + ∑ x ∈ s, (x * 2) := by
  Hint "Apply the cons decomposition lemma: `rw [Finset.sum_cons]`
  or `exact Finset.sum_cons ha`."
  Hint (hidden := true) "Try `exact Finset.sum_cons ha`."
  exact Finset.sum_cons ha

Conclusion
"
You applied `Finset.sum_cons` to split off the first element of a
`cons`-constructed finset.

## `cons` vs `insert`

Recall:
- `Finset.cons a s h` **requires** a proof `h : a ∉ s` upfront.
- `Finset.insert a s` uses `DecidableEq` to insert `a`, and is a
  no-op if `a ∈ s`.

Both have corresponding sum lemmas. Next you will see `sum_insert`.
"

/-- `Finset.sum_cons` states that
`∑ x ∈ Finset.cons a s h, f x = f a + ∑ x ∈ s, f x`.

This decomposes a sum over `cons a s h` into the term at `a` plus
the sum over `s`. -/
TheoremDoc Finset.sum_cons as "Finset.sum_cons" in "Finset"

NewTheorem Finset.sum_cons
DisabledTactic trivial decide native_decide simp aesop simp_all
