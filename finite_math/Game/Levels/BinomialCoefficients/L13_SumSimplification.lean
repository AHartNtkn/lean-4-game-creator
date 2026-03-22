import Game.Metadata

World "BinomialCoefficients"
Level 13

Title "Coaching: Single-Term Sums"

Introduction "
# Simplifying a Single-Term Sum

Before tackling the hockey stick identity, let's practice a pattern
that will appear in its base case: **simplifying a sum with one term**.

A sum over `Finset.range 1` has exactly one term (at index $0$).
To simplify it:
1. `Finset.sum_range_succ` peels off the last term: $\\sum_{i=0}^{0} f(i) = (\\sum_{i \\in \\emptyset} f(i)) + f(0)$
2. `Finset.sum_range_zero` clears the empty sum: $\\sum_{i \\in \\emptyset} f(i) = 0$
3. `zero_add` simplifies: $0 + f(0) = f(0)$

After the sum is simplified, you'll need to show that
$\\binom{0}{k} = \\binom{1}{k+1}$. This requires expanding the right
side with Pascal's identity, then using the **collect-and-close**
pattern: bring $\\binom{0}{k+1} = 0$ into context with `have`, then
simplify with `add_zero`.
"

/-- A single-term sum of choose: ∑ i in range 1, choose i k = choose 1 (k+1). -/
Statement (k : ℕ) :
    ∑ i ∈ Finset.range 1, Nat.choose i k = Nat.choose 1 (k + 1) := by
  Hint "First, simplify the single-term sum.
  Use `sum_range_succ` to peel, `sum_range_zero` to clear,
  and `zero_add` to simplify."
  Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]`."
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  Hint "The goal is `Nat.choose 0 k = Nat.choose 1 (k + 1)`.

  Expand the right side with Pascal's identity."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]
  Hint "The goal is `Nat.choose 0 k = Nat.choose 0 k + Nat.choose 0 (k + 1)`.

  You can't choose $k + 1$ items from $0$ items, so
  `Nat.choose 0 (k+1) = 0`. Bring this into context with `have`,
  then rewrite."
  Hint (hidden := true) "Try:
  `have h : Nat.choose 0 (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)`
  `rw [h, add_zero]`"
  have h : Nat.choose 0 (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h, add_zero]

Conclusion "
You practiced the **single-term sum** pattern:
1. `sum_range_succ` + `sum_range_zero` + `zero_add` to reduce to a single term
2. `choose_succ_succ` to expand Pascal's identity
3. **Collect-and-close**: bring `choose 0 (k+1) = 0` into context with `have`,
   then simplify with `add_zero`

This is exactly the base case of the hockey stick identity coming up next.
By practicing it here, you can focus on the inductive step in the next level.
"

NewTheorem zero_add add_comm

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
