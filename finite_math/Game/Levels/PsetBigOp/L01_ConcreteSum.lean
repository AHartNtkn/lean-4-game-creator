import Game.Metadata

World "PsetBigOp"
Level 1

Title "Concrete Sum Computation"

Introduction "
# Warm-Up: Compute a Sum

Compute $\\sum_{x \\in \\{2, 5, 8\\}} f(x)$ by peeling elements
one at a time, given the value of $f$ at each element.

You'll need:
- `Finset.sum_insert h` to peel each element (proving `h : a \\notin s`)
- `Finset.sum_singleton` for the final singleton
- Hypothesis substitution (`rw [hf2, ...]`) for the function values
"

/-- Compute the sum of f over the finset {2, 5, 8} given f's values. -/
Statement (f : ℕ → ℕ) (hf2 : f 2 = 3) (hf5 : f 5 = 6) (hf8 : f 8 = 9) :
    ∑ x ∈ ({2, 5, 8} : Finset ℕ), f x = 18 := by
  Hint (hidden := true) "Prove non-membership and peel with `sum_insert`.
  Pattern: `have h : (2 : ℕ) ∉ (insert 5 (singleton 8) : Finset ℕ) := by ...`
  then `rw [Finset.sum_insert h]`."
  have h1 : (2 : ℕ) ∉ ({5, 8} : Finset ℕ) := by
    rw [Finset.mem_insert, Finset.mem_singleton]; omega
  rw [Finset.sum_insert h1]
  Hint (hidden := true) "Now peel `5` from the remaining set.
  `have h : (5 : ℕ) ∉ (singleton 8 : Finset ℕ) := by
    rw [Finset.mem_singleton]; omega`
  then `rw [Finset.sum_insert h]`."
  have h2 : (5 : ℕ) ∉ ({8} : Finset ℕ) := by
    rw [Finset.mem_singleton]; omega
  rw [Finset.sum_insert h2]
  Hint (hidden := true) "Use `rw [Finset.sum_singleton]` to evaluate the
  singleton sum, then substitute the function values:
  `rw [hf2, hf5, hf8]`."
  rw [Finset.sum_singleton, hf2, hf5, hf8]
  Hint (hidden := true) "The remaining arithmetic `3 + (6 + 9) = 18`
  is closed by `omega`."
  omega

Conclusion "
You computed $\\sum_{x \\in \\{2,5,8\\}} f(x) = f(2) + f(5) + f(8) = 3 + 6 + 9 = 18$
by peeling elements with `sum_insert` and proving non-membership at
each step. This is the same insert-peel pattern from BigOpIntro,
applied to a fresh finset with an abstract function.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_cons
