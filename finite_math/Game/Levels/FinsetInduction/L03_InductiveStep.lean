import Game.Metadata

World "FinsetInduction"
Level 3

Title "Practicing the Inductive Step"

Introduction "
# The Inductive Step Pattern

The inductive step is where finset induction gets interesting.
You're given:
- A finset `s` and a fresh element `a` with `ha : a \\notin s`
- The induction hypothesis `ih`: the identity holds for `s`

And you must prove the identity for `insert a s`.

The standard pattern is:

1. **Peel**: Use `Finset.sum_insert ha` to split the sum over
   `insert a s` into `f a + \\sum_{x \\in s} f(x)`
2. **Apply IH**: Rewrite with the induction hypothesis `ih`
3. **Close**: Use `ring` (or `omega`) to finish the arithmetic

**Your task**: You're in the inductive step of the identity
$\\sum_{x \\in s} (f(x) + f(x)) = 2 \\cdot \\sum_{x \\in s} f(x)$.

The hypotheses `ha` and `ih` are already provided. Complete the
proof for `insert a s`.
"

/-- The inductive step: given IH for s, prove for insert a s. -/
Statement (a : ℕ) (s : Finset ℕ) (f : ℕ → ℕ) (ha : a ∉ s)
    (ih : ∑ x ∈ s, (f x + f x) = 2 * ∑ x ∈ s, f x) :
    ∑ x ∈ insert a s, (f x + f x) = 2 * ∑ x ∈ insert a s, f x := by
  Hint "**Step 1 — Peel**: Use `Finset.sum_insert ha` to split both
  sums over `insert a s`. The left side becomes
  `(f a + f a) + ∑ x ∈ s, (f x + f x)`, and the right side
  becomes `2 * (f a + ∑ x ∈ s, f x)`."
  Hint (hidden := true) "Try `rw [Finset.sum_insert ha]`.
  You'll need to apply it to both sides — use
  `rw [Finset.sum_insert ha, Finset.sum_insert ha]`."
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  Hint "**Step 2 — Apply IH**: The induction hypothesis `ih` tells
  you that `∑ x ∈ s, (f x + f x) = 2 * ∑ x ∈ s, f x`.
  Use `rw [ih]` to substitute."
  Hint (hidden := true) "Try `rw [ih]`."
  rw [ih]
  Hint "**Step 3 — Close**: The goal is now pure arithmetic:
  `f a + f a + 2 * ∑ f = 2 * (f a + ∑ f)`.
  Use `ring` to close it."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
The inductive step pattern for sum identities:

1. **Peel** both sides with `sum_insert ha`
2. **Apply** the induction hypothesis `ih`
3. **Close** the arithmetic with `ring`

The key insight: `sum_insert ha` is the bridge between the sum
over `insert a s` and the sum over `s` (where the IH applies).
Without the non-membership proof `ha`, the peel step can't fire —
this is why finset induction gives you `a \\notin s` as a hypothesis.

In the next level, you'll combine the base case and inductive step
into a complete induction proof.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub
