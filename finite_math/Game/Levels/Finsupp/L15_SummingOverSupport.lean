import Game.Metadata

World "Finsupp"
Level 15

Title "Summing Over the Support"

Introduction "
# Connecting Finsupp to Big Operators

Every finitely supported function can be decomposed as a sum over its
support. For `Finsupp.single 3 7`, the support is `{3}`, and summing
the function values over this singleton gives `7`.

This connects finitely supported functions back to the big operator
machinery from earlier worlds. The key idea:

`∑ a ∈ f.support, f a`

computes the **total mass** of `f` — the sum of all its nonzero values.
For a single, this is just the value at the one nonzero point.

To evaluate this sum, you will:
1. Compute the support using `support_single_ne_zero`
2. Simplify the sum over a singleton using `Finset.sum_singleton`
3. Evaluate the function at the support point using `single_eq_same`

**Your task**: Compute the total mass of `Finsupp.single 3 7`.
"

/-- Sum the values of a single over its support. -/
Statement : ∑ a ∈ (Finsupp.single 3 7 : ℕ →₀ ℕ).support, (Finsupp.single 3 7 : ℕ →₀ ℕ) a = 7 := by
  Hint "First, compute the support. You know from Level 3 that the
  support of a nonzero single is a singleton."
  Hint (hidden := true) "Try
  `rw [Finsupp.support_single_ne_zero 3 (show (7 : ℕ) ≠ 0 by omega)]`.
  This rewrites the support to `singleton 3`."
  rw [Finsupp.support_single_ne_zero 3 (show (7 : ℕ) ≠ 0 by omega)]
  Hint "The sum is now over a singleton set. Use `Finset.sum_singleton`
  to simplify `∑ a ∈ singleton 3, f a` to `f 3`."
  Hint (hidden := true) "Try `rw [Finset.sum_singleton]`."
  rw [Finset.sum_singleton]
  Hint "Now evaluate the single at its support point."
  Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
  rw [Finsupp.single_eq_same]

Conclusion "
You just computed `∑ a ∈ f.support, f a = 7` for `f = single 3 7`.
This is the total mass of the function — the sum of all nonzero values.

The pattern — compute support, simplify the Finset sum, evaluate —
connects three ideas:
- **Finsupp.support** (from this world) tells you *where* the function
  is nonzero
- **Finset.sum** (from BigOp worlds) sums over a finite set
- **Evaluation lemmas** (single_eq_same, single_eq_of_ne) compute the
  function values

In Mathlib, the operation `Finsupp.sum f g` computes
`∑ a ∈ f.support, g a (f a)`. The decomposition theorem
`f.sum Finsupp.single = f` says every finitely supported function
equals the sum of its singles — this is the formal version of writing
a polynomial as a sum of monomials, or a vector as a sum of basis
vectors scaled by coordinates.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply Finsupp.single_add
