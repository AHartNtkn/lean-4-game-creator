import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 8

Title "A reindexing proof"

Introduction
"
# Reindexing practice: shifting a general sum

In the previous level, you reindexed a concrete sum with specific
numbers. Now let us do it with a general shift.

## The statement

Prove:
$$\\sum_{i=0}^{n-1} (i + 1) = \\sum_{j=1}^{n} j$$

In Lean notation:
```
∑ i ∈ range n, (i + 1) = ∑ j ∈ Ico 1 (n + 1), j
```

## Strategy

Use `Finset.sum_nbij'` with:
- Forward map: `i ↦ i + 1` (shift up)
- Inverse map: `j ↦ j - 1` (shift down)

This is the same structure as the previous level, but with variables
instead of constants. The membership and inverse obligations will need
`omega` or simple arithmetic.
"

/-- Reindexing a general shifted sum. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (i + 1) = ∑ j ∈ Finset.Ico 1 (n + 1), j := by
  Hint "Apply `Finset.sum_nbij'` with the forward map `(· + 1)` and
  the inverse `(· - 1)`, just like the previous level but now with
  the variable `n`.

  Try `apply Finset.sum_nbij' (· + 1) (· - 1)`."
  Hint (hidden := true) "Try `apply Finset.sum_nbij' (· + 1) (· - 1)`."
  apply Finset.sum_nbij' (· + 1) (· - 1)
  · Hint "Show `a + 1 ∈ Ico 1 (n + 1)` when `a ∈ range n`.

    Try `intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Ico]; omega`."
    Hint (hidden := true) "Try `intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Ico]; omega`."
    intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico]
    omega
  · Hint "Show `a - 1 ∈ range n` when `a ∈ Ico 1 (n + 1)`.

    Try `intro a ha; simp only [Finset.mem_Ico] at ha; simp only [Finset.mem_range]; omega`."
    Hint (hidden := true) "Try `intro a ha; simp only [Finset.mem_Ico] at ha; simp only [Finset.mem_range]; omega`."
    intro a ha
    simp only [Finset.mem_Ico] at ha
    simp only [Finset.mem_range]
    omega
  · Hint "Prove the left-inverse property. Use `omega`."
    Hint (hidden := true) "Try `intro a _; omega`."
    intro a _; omega
  · Hint "Prove the right-inverse property. Use membership info + `omega`."
    Hint (hidden := true) "Try `intro a ha; simp only [Finset.mem_Ico] at ha; omega`."
    intro a ha
    simp only [Finset.mem_Ico] at ha
    omega
  · Hint "Prove the function values match: `a + 1 = id (a + 1)`.
    This is `rfl`."
    Hint (hidden := true) "Try `intro a _; rfl`."
    intro a _; rfl

Conclusion
"
You proved a general reindexing identity using `Finset.sum_nbij'`!

## The reindexing principle

In general, to prove `∑ i ∈ s, f i = ∑ j ∈ t, g j` by reindexing:

1. Find a bijection `φ : s → t` such that `f i = g (φ i)`.
2. Find the inverse `ψ : t → s`.
3. Apply `sum_nbij' φ ψ` and prove the five obligations.

## Alternative: `Finset.sum_equiv`

When you have a full `Equiv` (a type-level bijection), you can use
`Finset.sum_equiv` instead of `sum_nbij'`:

```
Finset.sum_equiv (e : ι ≃ κ)
  (hst : ∀ i, i ∈ s ↔ e i ∈ t)
  (hfg : ∀ i ∈ s, f i = g (e i))
  : ∑ i ∈ s, f i = ∑ i ∈ t, g i
```

This has fewer obligations (two instead of five) because the `Equiv`
already packages the bijection data.

## Transfer

In ordinary mathematics, you would write: \"Setting $j = i + 1$,
the sum becomes ...\" This informal substitution is exactly what
`sum_nbij'` formalizes. The five obligations are the rigorous
version of checking that the substitution is valid.

## What comes next

The boss level combines filtering, splitting, and double-sum
techniques in a single proof.
"

/-- `Finset.sum_equiv` reindexes a sum using an `Equiv`.

Given `e : ι ≃ κ`, membership compatibility, and function compatibility,
it proves `∑ i ∈ s, f i = ∑ i ∈ t, g i`. Fewer obligations than
`sum_nbij'` because the `Equiv` packages the bijection. -/
TheoremDoc Finset.sum_equiv as "Finset.sum_equiv" in "Finset"

NewTheorem Finset.sum_equiv
DisabledTactic trivial decide native_decide simp aesop simp_all
