import Game.Metadata

World "BigOpAlgebra"
Level 10

Title "Reordering for Simplification"

Introduction "
# When Swapping Makes Things Simpler

The power of `sum_comm` isn't just rearranging — it's that one
summation order might make the inner sum easy to evaluate while
the other doesn't.

If you know the value of each column sum `∑ x ∈ s, f x y` for
every `y ∈ t`, you can compute the total by:

1. **Swap** the summation order with `sum_comm`
2. **Replace** each inner sum with its known value using `sum_congr`
3. **Evaluate** the resulting constant sum with `sum_const`

This is the grid picture from L08: sum by columns instead of rows,
because the column totals are known.

**Your task**: Given that every column sum equals 10, compute the
grand total of the double sum.
"

/-- Use sum_comm to enable simplification of the inner sum. -/
Statement (s t : Finset ℕ) (f : ℕ → ℕ → ℕ)
    (h : ∀ y ∈ t, ∑ x ∈ s, f x y = 10) :
    ∑ x ∈ s, ∑ y ∈ t, f x y = t.card • 10 := by
  Hint "The inner sums `∑ y ∈ t, f x y` have no known value. But
  the column sums `∑ x ∈ s, f x y` are all 10. Swap the order
  with `rw [Finset.sum_comm]`."
  rw [Finset.sum_comm]
  Hint "Now the inner sum is `∑ x ∈ s, f x y`, which equals 10
  for each `y ∈ t`. Use `rw [Finset.sum_congr rfl h]` to
  replace each inner sum with 10."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl h]`."
  rw [Finset.sum_congr rfl h]
  Hint "The sum is now `∑ y ∈ t, 10` — a constant sum. Use
  `exact Finset.sum_const 10`."
  Hint (hidden := true) "Try `exact Finset.sum_const 10`."
  exact Finset.sum_const 10

Conclusion "
You just saw the real power of `sum_comm`: it doesn't just
rearrange — it **enables simplification**. By choosing the right
summation order, you make the inner sum evaluatable.

This is exactly how **double-counting arguments** work in
combinatorics: count rows first or columns first — one direction
might be much easier to evaluate.

| Step | What it does |
|------|-------------|
| `sum_comm` | Swap to the easier order |
| `sum_congr rfl h` | Substitute known inner sums |
| `sum_const c` | Evaluate the constant outer sum |
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
