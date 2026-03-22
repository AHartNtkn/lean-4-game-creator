import Game.Metadata

World "BigOpAlgebra"
Level 2

Title "Products Distribute Over Multiplication"

Introduction "
# The Multiplicative Twin

Just as summation distributes addition:
$$\\sum(f + g) = \\sum f + \\sum g$$

products distribute multiplication:
$$\\prod_{x \\in s} \\bigl(f(x) \\cdot g(x)\\bigr) = \\Bigl(\\prod_{x \\in s} f(x)\\Bigr) \\cdot \\prod_{x \\in s} g(x)$$

In Lean:
```
Finset.prod_mul_distrib :
  ∏ x ∈ s, (f x * g x) = (∏ x ∈ s, f x) * ∏ x ∈ s, g x
```

This duality — sums with `+` correspond to products with `*` —
runs through all of big-operator theory.

**Your task**: Given the individual products of `f` and `g`,
compute the product of `f * g` using `prod_mul_distrib`.
"

/-- Using prod_mul_distrib with known component products. -/
Statement (s : Finset ℕ) (f g : ℕ → ℕ) (a b : ℕ)
    (hf : ∏ x ∈ s, f x = a) (hg : ∏ x ∈ s, g x = b) :
    ∏ x ∈ s, (f x * g x) = a * b := by
  Hint "Use `rw [Finset.prod_mul_distrib]` to split the product
  into `(∏ x ∈ s, f x) * ∏ x ∈ s, g x`."
  rw [Finset.prod_mul_distrib]
  Hint "Now substitute the known values."
  Hint (hidden := true) "Try `rw [hf, hg]`."
  rw [hf, hg]

Conclusion "
`prod_mul_distrib` is the multiplicative analogue of
`sum_add_distrib`. The same transform-substitute-close pattern
works for products.

| Additive | Multiplicative |
|----------|---------------|
| `∑(f + g) = ∑f + ∑g` | `∏(f · g) = ∏f · ∏g` |
| `sum_add_distrib` | `prod_mul_distrib` |

Many sum lemmas have product twins, and the proofs are
structurally identical.
"

/-- `Finset.prod_mul_distrib` states that
`∏ x ∈ s, (f x * g x) = (∏ x ∈ s, f x) * ∏ x ∈ s, g x`.

Products distribute over multiplication.

## Syntax
```
exact Finset.prod_mul_distrib
rw [Finset.prod_mul_distrib]
```

## When to use it
When the goal has `∏ x ∈ s, (f x * g x)` and you want to split
it into `∏ f · ∏ g`, or vice versa.
-/
TheoremDoc Finset.prod_mul_distrib as "Finset.prod_mul_distrib" in "BigOp"

NewTheorem Finset.prod_mul_distrib

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
