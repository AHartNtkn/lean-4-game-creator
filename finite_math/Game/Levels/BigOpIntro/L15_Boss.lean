import Game.Metadata

World "BigOpIntro"
Level 15

Title "Boss: The Full Toolkit"

Introduction "
# Boss: Integrate Everything

You have the complete big-operator toolkit:
- **Base cases**: empty sum = 0, empty product = 1
- **Singleton**: sum/product over one element = function value
- **Insert**: peel off one element at a time
- **Congruence**: rewrite the function inside a sum/product
- **Cardinality bridge**: `s.card = ∑ x ∈ s, 1`

This boss tests these in one proof with three parts:

**Part 1**: Use the cardinality-summation bridge.

**Part 2**: Compute $\\sum_{{x \\in \\{1,2,3\\}}} f(x)$ where $f(x) = x$,
getting $1 + 2 + 3 = 6$.

**Part 3**: Compute $\\prod_{{x \\in \\{1,2,3\\}}} f(x)$ with the same $f$,
getting $1 \\cdot 2 \\cdot 3 = 6$.
"

/-- Integrate the full big-operator toolkit. -/
Statement (f : ℕ → ℕ) (hf : ∀ x ∈ ({1, 2, 3} : Finset ℕ), f x = x)
    (s : Finset ℕ) (hs : ∑ x ∈ s, 1 = 5) :
    (s.card = 5) ∧
    (∑ x ∈ ({1, 2, 3} : Finset ℕ), f x = 6) ∧
    (∏ x ∈ ({1, 2, 3} : Finset ℕ), f x = 6) := by
  Hint "The goal is a three-way conjunction. Use `constructor` to
  split off the first part."
  constructor
  · -- Part 1: card bridge
    Hint "Use `Finset.card_eq_sum_ones` to rewrite `s.card` as a sum
    of ones, then apply the hypothesis `hs`."
    Hint (hidden := true) "Try `rw [Finset.card_eq_sum_ones]` then
    `exact hs`."
    rw [Finset.card_eq_sum_ones]
    exact hs
  · Hint "Use `constructor` again to split the remaining conjunction."
    constructor
    · -- Part 2: Sum computation
      Hint "The function `f` is abstract. Use `sum_congr` to replace
      `f x` with `x` inside the sum."
      Hint (hidden := true) "Create a helper:
      `have hsimp : ∑ x ∈ (... : Finset ℕ), f x = ∑ x ∈ ..., x := by
        apply Finset.sum_congr rfl; exact hf`
      Then `rw [hsimp]`."
      have hsimp : ∑ x ∈ ({1, 2, 3} : Finset ℕ), f x =
          ∑ x ∈ ({1, 2, 3} : Finset ℕ), x := by
        apply Finset.sum_congr rfl
        exact hf
      rw [hsimp]
      Hint "Now peel elements with `sum_insert`. Prove non-membership
      first."
      have h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ) := by
        rw [Finset.mem_insert, Finset.mem_singleton]; omega
      rw [Finset.sum_insert h1]
      Hint "Peel the next element."
      have h2 : (2 : ℕ) ∉ ({3} : Finset ℕ) := by
        rw [Finset.mem_singleton]; omega
      rw [Finset.sum_insert h2]
      Hint "Close the singleton sum, then finish the arithmetic."
      rw [Finset.sum_singleton]
      Hint (hidden := true) "Close with `omega`."
      omega
    · -- Part 3: Product computation
      Hint "Same pattern for products: use `prod_congr` to simplify,
      then peel with `prod_insert`."
      Hint (hidden := true) "Create a helper:
      `have hsimp : ∏ x ∈ (... : Finset ℕ), f x = ∏ x ∈ ..., x := by
        apply Finset.prod_congr rfl; exact hf`
      Then `rw [hsimp]`."
      have hsimp : ∏ x ∈ ({1, 2, 3} : Finset ℕ), f x =
          ∏ x ∈ ({1, 2, 3} : Finset ℕ), x := by
        apply Finset.prod_congr rfl
        exact hf
      rw [hsimp]
      Hint "Peel elements with `prod_insert`."
      have h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ) := by
        rw [Finset.mem_insert, Finset.mem_singleton]; omega
      rw [Finset.prod_insert h1]
      have h2 : (2 : ℕ) ∉ ({3} : Finset ℕ) := by
        rw [Finset.mem_singleton]; omega
      rw [Finset.prod_insert h2]
      Hint "Close the singleton product, then verify the arithmetic."
      rw [Finset.prod_singleton]
      Hint (hidden := true) "The multiplication `1 * (2 * 3) = 6` is
      concrete arithmetic. Try `omega`."
      omega

Conclusion "
Congratulations! You've mastered the Big Operators Introduction.

You can now:
- **Compute** sums and products by peeling with
  `sum_insert`/`prod_insert` and closing with
  `sum_singleton`/`prod_singleton`
- **Simplify** summands/factors pointwise with `sum_congr`/`prod_congr`
- **Connect** cardinality to summation via `card_eq_sum_ones`
- **Distinguish** the base cases: empty sum = 0, empty product = 1

The complete toolkit:

| Lemma | What it does |
|-------|-------------|
| `sum_empty` / `prod_empty` | Empty sum = 0, empty product = 1 |
| `sum_singleton` / `prod_singleton` | Singleton = function value |
| `sum_insert h` / `prod_insert h` | Peel one element (needs `h : a ∉ s`) |
| `sum_congr rfl` / `prod_congr rfl` | Rewrite the summand/factor pointwise |
| `card_eq_sum_ones` | Cardinality = sum of 1 |

**Looking ahead**: The next world introduces algebraic manipulation
of big operators. A key tool will be `Finset.sum_range_succ`, which
unfolds sums over `Finset.range` one element at a time:

`∑ i in range (n+1), f i = (∑ i in range n, f i) + f n`

This is the **split-off-the-last-term** strategy: to evaluate or prove
something about a sum over `range (n+1)`, split off the last term and
reduce to a statement about `range n`. This is finset induction on
ranges — the engine that drives inductive proofs about summation
formulas, and it foreshadows the general finset induction principle
you'll meet later.
"

/-- `ext` proves that two objects of the same type are equal by showing
their components are equal.

## Warning
In this level, `ext` is disabled because the goal is to learn
`sum_congr` / `prod_congr` — the big-operator-specific way to
prove equality of sums by rewriting the summand.
-/
TacticDoc ext

/-- `congr` proves equality by reducing to equality of subexpressions.

## Warning
In this level, `congr` is disabled because the goal is to learn
`sum_congr` / `prod_congr` — the big-operator-specific way to
prove equality of sums by rewriting the summand.
-/
TacticDoc congr

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext congr rfl
DisabledTheorem Finset.sum_pair Finset.prod_pair
