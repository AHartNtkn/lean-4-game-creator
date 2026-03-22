import Game.Metadata

World "BigOpAlgebra"
Level 1

Title "Splitting a Sum of Sums"

Introduction "
# Linearity of ∑: Splitting Addition

In ordinary math, summation is **linear** — you can split a sum of
sums into separate sums:

$$\\sum_{x \\in s} \\bigl(f(x) + g(x)\\bigr) = \\sum_{x \\in s} f(x) + \\sum_{x \\in s} g(x)$$

In Lean, this is `Finset.sum_add_distrib`:

```
Finset.sum_add_distrib :
  ∑ x ∈ s, (f x + g x) = (∑ x ∈ s, f x) + ∑ x ∈ s, g x
```

This is the big-operator analogue of distributing addition over a
loop: instead of adding `f(x) + g(x)` at each step, you can
separately sum all the `f(x)` values and all the `g(x)` values,
then add the totals.

**Your task**: You know the individual sums of `f` and `g` over `s`.
Use `sum_add_distrib` to split the combined sum, then substitute
the known values.
"

/-- Using sum_add_distrib with known component sums. -/
Statement (s : Finset ℕ) (f g : ℕ → ℕ)
    (hf : ∑ x ∈ s, f x = 10) (hg : ∑ x ∈ s, g x = 7) :
    ∑ x ∈ s, (f x + g x) = 17 := by
  Hint "Use `rw [Finset.sum_add_distrib]` to split the sum into
  `(∑ x ∈ s, f x) + ∑ x ∈ s, g x`."
  rw [Finset.sum_add_distrib]
  Hint "Now substitute the known values with `rw [hf, hg]`."
  Hint (hidden := true) "Try `rw [hf, hg]`."
  rw [hf, hg]

Conclusion "
The pattern you just used will recur throughout this world:

1. **Transform** the sum structure with a big-operator lemma
2. **Substitute** known values with `rw`
3. **Close** the arithmetic (if needed)

`sum_add_distrib` is the linearity of summation — one of the
most-used algebraic properties of big operators.

**When to use it**: Whenever you see `∑ x ∈ s, (... + ...)` and
want to separate the two parts into independent sums.
"

/-- `Finset.sum_add_distrib` states that
`∑ x ∈ s, (f x + g x) = (∑ x ∈ s, f x) + ∑ x ∈ s, g x`.

Summation distributes over addition — you can split a sum of sums
into separate sums.

## Syntax
```
exact Finset.sum_add_distrib
rw [Finset.sum_add_distrib]
```

## When to use it
When the goal has `∑ x ∈ s, (f x + g x)` and you want to split
it into `∑ f + ∑ g`, or vice versa.

## Example
```
-- Goal: ∑ x ∈ s, (f x + g x) = (∑ x ∈ s, f x) + ∑ x ∈ s, g x
exact Finset.sum_add_distrib
```
-/
TheoremDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "BigOp"

TheoremTab "BigOp"
NewTheorem Finset.sum_add_distrib

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
