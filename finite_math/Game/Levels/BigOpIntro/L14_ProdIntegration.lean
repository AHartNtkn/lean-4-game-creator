import Game.Metadata

World "BigOpIntro"
Level 14

Title "Product: Congr + Peel"

Introduction "
# Combining prod_congr with Peeling

You just practiced `prod_congr` on its own. Now combine it with
the peel pattern to compute a concrete product from an abstract
function.

The three-step pattern:
1. **Congr**: `apply Finset.prod_congr rfl` to simplify the factor
2. **Peel**: `prod_insert h` to extract elements one at a time
3. **Close**: `prod_singleton` to evaluate the last element

**Your task**: Given that `f x = x` on the finset `{2, 5}`, compute
the product of `f` over that finset.
"

/-- Compute a product by simplifying and unfolding. -/
Statement (f : ℕ → ℕ) (hf : ∀ x ∈ ({2, 5} : Finset ℕ), f x = x) :
    ∏ x ∈ ({2, 5} : Finset ℕ), f x = 2 * 5 := by
  Hint "The function `f` is abstract — you can't unfold the product
  directly. Start by using `prod_congr` to replace `f x` with `x`."
  Hint (hidden := true) "Create a helper:
  `have hsimp : ∏ x ∈ (... : Finset ℕ), f x = ∏ x ∈ (... : Finset ℕ), x := by
    apply Finset.prod_congr rfl; exact hf`
  Then `rw [hsimp]`."
  have hsimp : ∏ x ∈ ({2, 5} : Finset ℕ), f x =
      ∏ x ∈ ({2, 5} : Finset ℕ), x := by
    apply Finset.prod_congr rfl
    exact hf
  rw [hsimp]
  Hint "Now the product has a concrete function. Prove non-membership
  and peel with `prod_insert`."
  Hint (hidden := true) "Use `have h : (2 : ℕ) ∉ (Finset.singleton 5) := by
  rw [Finset.mem_singleton]; omega`"
  have h : (2 : ℕ) ∉ ({5} : Finset ℕ) := by
    rw [Finset.mem_singleton]; omega
  rw [Finset.prod_insert h]
  Hint "Close the singleton product."
  rw [Finset.prod_singleton]

Conclusion "
You've computed a product using the congr-peel-close pattern:

1. **Congr**: `prod_congr rfl` to simplify the factor
2. **Peel**: `prod_insert h` to extract one element
3. **Close**: `prod_singleton` to evaluate the base case

$$\\prod_{{x \\in \\{2, 5\\}}} f(x) = f(2) \\cdot f(5) = 2 \\cdot 5 = 10$$

`prod_congr` is the multiplicative twin of `sum_congr`. The API
for `∑` and `∏` is systematically parallel:

| Sum | Product |
|-----|---------|
| `sum_empty` | `prod_empty` |
| `sum_singleton` | `prod_singleton` |
| `sum_insert` | `prod_insert` |
| `sum_congr` | `prod_congr` |
"

/-- `ext` proves that two objects of the same type are equal by showing
their components are equal.

## Warning
In this level, `ext` is disabled because the goal is to learn
`prod_congr` — the big-operator-specific way to prove equality of
products by rewriting the factor.
-/
TacticDoc ext

/-- `congr` proves equality by reducing to equality of subexpressions.

## Warning
In this level, `congr` is disabled because the goal is to learn
`prod_congr` — the big-operator-specific way to prove equality of
products by rewriting the factor.
-/
TacticDoc congr

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext congr rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
