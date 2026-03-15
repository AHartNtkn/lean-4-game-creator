import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 7

Title "Basic reindexing"

Introduction
"
# Reindexing: changing the index of a sum

In ordinary mathematics, you change variables in a sum freely:

$$\\sum_{i=0}^{n-1} f(i+1) = \\sum_{j=1}^{n} f(j)
\\quad \\text{(setting } j = i+1\\text{)}$$

In Lean, this is formalized by `Finset.sum_nbij'`: given a bijection
between two finsets, you can transform one sum into the other.

```
Finset.sum_nbij' (i : ι → κ) (j : κ → ι)
  (hi : ∀ a ∈ s, i a ∈ t)       -- i maps s into t
  (hj : ∀ a ∈ t, j a ∈ s)       -- j maps t into s
  (left_inv : ∀ a ∈ s, j (i a) = a)   -- j ∘ i = id on s
  (right_inv : ∀ a ∈ t, i (j a) = a)  -- i ∘ j = id on t
  (h : ∀ a ∈ s, f a = g (i a))  -- f and g agree via i
  : ∑ x ∈ s, f x = ∑ x ∈ t, g x
```

This looks complex, but the idea is simple: provide a bijection and
prove the five obligations.

## Your task

Prove: `∑ i ∈ range 4, (i + 5) = ∑ j ∈ Ico 5 9, j`.

The bijection is `i ↦ i + 5` with inverse `j ↦ j - 5`.

Use `apply Finset.sum_nbij' (· + 5) (· - 5)` to start, then prove
each obligation.
"

/-- Reindexing a sum via a shift. -/
Statement :
    ∑ i ∈ Finset.range 4, (i + 5) = ∑ j ∈ Finset.Ico 5 9, j := by
  Hint "Apply `Finset.sum_nbij'` with the forward map `(· + 5)` and
  the inverse map `(· - 5)`. This sets up five proof obligations.

  Try `apply Finset.sum_nbij' (· + 5) (· - 5)`."
  Hint (hidden := true) "Try `apply Finset.sum_nbij' (· + 5) (· - 5)`."
  apply Finset.sum_nbij' (· + 5) (· - 5)
  Hint "Now you have five goals. The first asks you to show that `i + 5`
  lands in `Ico 5 9` when `i ∈ range 4`.

  Start with `intro a ha` to introduce the element and its membership."
  · Hint "Introduce the element and its membership proof."
    Hint (hidden := true) "Try `intro a ha`."
    intro a ha
    Hint "Now show `a + 5 ∈ Finset.Ico 5 9`. Use `simp only` to
    unfold the membership predicates, then `omega` to close the
    arithmetic.

    Try:
    ```
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico]
    omega
    ```"
    Hint (hidden := true) "Try `simp only [Finset.mem_range] at ha; simp only [Finset.mem_Ico]; omega`."
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico]
    omega
  · Hint "Show that `j - 5` lands in `range 4` when `j ∈ Ico 5 9`.

    Try `intro a ha; simp only [Finset.mem_Ico] at ha; simp only [Finset.mem_range]; omega`."
    Hint (hidden := true) "Try `intro a ha; simp only [Finset.mem_Ico] at ha; simp only [Finset.mem_range]; omega`."
    intro a ha
    simp only [Finset.mem_Ico] at ha
    simp only [Finset.mem_range]
    omega
  · Hint "Show that `(a + 5) - 5 = a`. Use `omega`."
    Hint (hidden := true) "Try `intro a _; omega`."
    intro a _; omega
  · Hint "Show that `(a - 5) + 5 = a` when `a ∈ Ico 5 9`. Use
    `omega` after introducing and simplifying."
    Hint (hidden := true) "Try `intro a ha; simp only [Finset.mem_Ico] at ha; omega`."
    intro a ha
    simp only [Finset.mem_Ico] at ha
    omega
  · Hint "Show that `a + 5 = id (a + 5)`, i.e., the function values
    match. This is definitionally true."
    Hint (hidden := true) "Try `intro a _; rfl`."
    intro a _; rfl

Conclusion
"
You completed your first reindexing proof using `Finset.sum_nbij'`!

## The five obligations

When you use `sum_nbij'` with a forward map `i` and inverse `j`, you
prove:
1. **Forward maps into target**: `i` sends `s` into `t`
2. **Inverse maps into source**: `j` sends `t` into `s`
3. **Left inverse**: `j (i a) = a` for `a ∈ s`
4. **Right inverse**: `i (j a) = a` for `a ∈ t`
5. **Function values match**: `f a = g (i a)` for `a ∈ s`

These correspond exactly to the conditions for a change of variables
in a sum.

## Practical tips

- The membership obligations often reduce to arithmetic; `omega` is
  your friend.
- The inverse obligations are usually immediate from the definitions.
- The function-value obligation is often `rfl` or `ring`.

## What comes next

The next level practices reindexing with a slightly more involved
example.
"

/-- `Finset.sum_nbij'` reindexes a sum using a bijection between finsets.

Given forward map `i : ι → κ`, inverse `j : κ → ι`, and proofs that
they form a bijection between `s` and `t` respecting the summand, it
proves `∑ x ∈ s, f x = ∑ x ∈ t, g x`. -/
TheoremDoc Finset.sum_nbij' as "Finset.sum_nbij'" in "Finset"

/-- `Finset.mem_Ico` states that `a ∈ Finset.Ico b c ↔ b ≤ a ∧ a < c`.

An element is in `Ico b c` if and only if it is at least `b` and
strictly less than `c`. -/
TheoremDoc Finset.mem_Ico as "Finset.mem_Ico" in "Finset"

NewTheorem Finset.sum_nbij' Finset.mem_Ico
DisabledTactic trivial decide native_decide simp aesop simp_all
