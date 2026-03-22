import Game.Metadata

World "BigOpIntro"
Level 7

Title "A Two-Element Product"

Introduction "
# Computing a Concrete Product

Now compute `∏ x ∈ s, f x` where `s` is a two-element finset — the
product of `f` over `{2, 3}`.

The pattern is identical to sums:
1. Substitute `s` with `rw [hs]`
2. Prove `2 ∉ {3}` and peel with `prod_insert`
3. Close with `prod_singleton`

**Your task**: Prove that `∏ x ∈ s, f x = f 2 * f 3`.
"

/-- Unfolding a two-element product with an abstract function. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hs : s = ({2, 3} : Finset ℕ)) :
    ∏ x ∈ s, f x = f 2 * f 3 := by
  Hint "Start by substituting `s` with `rw [hs]`."
  rw [hs]
  Hint "The pattern is the same as for sums. Prove that 2 is
  not in the singleton containing 3."
  Hint (hidden := true) "Use `have h : (2 : ℕ) ∉ (Finset.singleton 3) := by
  rw [Finset.mem_singleton]; omega`"
  have h : (2 : ℕ) ∉ ({3} : Finset ℕ) := by
    rw [Finset.mem_singleton]; omega
  Hint "Now use `rw [Finset.prod_insert h]` to peel off the 2."
  rw [Finset.prod_insert h]
  Hint "Use `rw [Finset.prod_singleton]` to evaluate the remaining
  singleton product."
  rw [Finset.prod_singleton]

Conclusion "
Products work exactly like sums, with `*` replacing `+` and `1`
replacing `0`. The same peel-and-simplify pattern applies.

**Two warnings to remember**:

1. The empty product is `1`, not `0`. In math: $\\prod_{{x \\in \\emptyset}} f(x) = 1$.
   This is analogous to $0! = 1$ — it's the multiplicative identity.

2. The empty sum is `0`, not `1`. Don't confuse the two base cases.

From now on, you have both `∑` and `∏` in your toolkit. Most of the
remaining levels focus on sums (they appear more often in practice),
but every sum technique has a product analogue.
"

NewTheorem Finset.prod_singleton Finset.prod_insert

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.sum_pair Finset.prod_pair
