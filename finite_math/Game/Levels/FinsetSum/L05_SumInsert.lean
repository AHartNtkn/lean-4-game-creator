import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 5

Title "sum_insert"

Introduction
"
# Decomposing a sum with `insert`

The `insert` version of the decomposition lemma is:

```
Finset.sum_insert (h : a ∉ s) :
  ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x
```

This is almost identical to `sum_cons`, but it uses `insert` instead
of `cons`. The key difference: `insert` requires `DecidableEq` on the
element type (which `Nat` has automatically), while `cons` requires
an explicit non-membership proof.

## Your task

Prove that for any finset `s : Finset Nat` and `a : Nat` with
`ha : a ∉ s`:

```
∑ x ∈ insert a s, (x + 1) = (a + 1) + ∑ x ∈ s, (x + 1)
```
"

/-- Decomposing a sum via `insert`. -/
Statement (s : Finset Nat) (a : Nat) (ha : a ∉ s) :
    ∑ x ∈ insert a s, (x + 1) = (a + 1) + ∑ x ∈ s, (x + 1) := by
  Hint "Apply `Finset.sum_insert`. It needs a proof that `a ∉ s`."
  Hint (hidden := true) "Use `rw [Finset.sum_insert ha]` or
  `exact Finset.sum_insert ha`."
  exact Finset.sum_insert ha

Conclusion
"
You used `Finset.sum_insert` — the `insert` analogue of `sum_cons`.

## When to use which

- Use `sum_cons` when the finset was built with `cons` (you have a
  proof of non-membership baked into the construction).
- Use `sum_insert` when the finset was built with `insert` (common
  in `Finset.induction_on` proofs, where the inductive step gives
  you `insert a s` with `ha : a ∉ s`).

In practice, `sum_insert` is more common because `Finset.induction_on`
produces `insert` steps.
"

/-- `Finset.sum_insert` states that if `a ∉ s`, then
`∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x`.

This is the `insert` version of the sum decomposition. It requires
`DecidableEq` on the element type. -/
TheoremDoc Finset.sum_insert as "Finset.sum_insert" in "Finset"

NewTheorem Finset.sum_insert
DisabledTactic trivial decide native_decide simp aesop simp_all
