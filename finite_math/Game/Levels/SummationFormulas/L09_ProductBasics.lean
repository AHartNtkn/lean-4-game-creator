import Game.Metadata

World "SummationFormulas"
Level 9

Title "A Constant Product"

Introduction "
# From Sums to Products

Every sum formula so far has used `sum_range_zero` (base) and
`sum_range_succ` (peel). Products over ranges have exact analogues:

- `Finset.prod_range_zero`: $\\prod_{i \\in \\text{range } 0} f(i) = 1$
  (the empty product is $1$, the multiplicative identity)
- `Finset.prod_range_succ`: peels off the last *factor* of a product

The induction pattern is identical — only the identity element changes
(0 for sums, 1 for products) and the operation changes (+ to *).

**Your task**: Prove that the constant product $\\prod_{i=0}^{n-1} 2 = 2^n$.
This is the product analogue of Level 1's $\\sum 1 = n$.
"

/-- `Finset.prod_range_zero` states that
`∏ k ∈ Finset.range 0, f k = 1`.

The product over an empty range is 1 (the identity for multiplication).

## Syntax
```
rw [Finset.prod_range_zero]
```

## When to use it
In the **base case** of a natural number induction proof about
products over `Finset.range`. Since `range 0 = ∅`, the product is 1.

## Connection
This is the product analogue of `Finset.sum_range_zero` (which gives 0).
The empty sum is 0 (additive identity); the empty product is 1
(multiplicative identity).
-/
TheoremDoc Finset.prod_range_zero as "Finset.prod_range_zero" in "BigOp"

/-- `Finset.prod_range_succ` states that
`∏ x ∈ Finset.range (n + 1), f x = (∏ x ∈ Finset.range n, f x) * f n`.

Peels off the last factor of a product over `Finset.range`.

## Syntax
```
rw [Finset.prod_range_succ]
```

## When to use it
In the **inductive step** of a natural number induction proof about
products over `Finset.range`. Separates `f n` from the rest, letting
you apply the induction hypothesis to the remaining product.

## Connection
This is the product analogue of `Finset.sum_range_succ` (which peels
the last term of a sum). It is also the range-based analogue of
`Finset.prod_insert` (which peels from `insert a s`).
-/
TheoremDoc Finset.prod_range_succ as "Finset.prod_range_succ" in "BigOp"

/-- The product of 2 over range n equals 2 to the n. -/
Statement (n : ℕ) : ∏ _i ∈ Finset.range n, (2 : ℕ) = 2 ^ n := by
  Hint "Induct on `n`. This follows the same pattern as the sum levels,
  but with `prod_range_zero` and `prod_range_succ` instead of
  their sum counterparts."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: The product over `range 0` is $1$.
    Use `prod_range_zero` and close with `ring`."
    Hint (hidden := true) "Try `rw [Finset.prod_range_zero]`
    then `ring`."
    rw [Finset.prod_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel the last factor with
    `prod_range_succ`, substitute the IH, and close with `ring`."
    Hint (hidden := true) "Try `rw [Finset.prod_range_succ, ih]`
    then `ring`."
    rw [Finset.prod_range_succ, ih]
    Hint "The goal is `2 ^ n * 2 = 2 ^ (n + 1)`.
    `ring` knows that $2^(n+1) = 2^n \\cdot 2$."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
You proved that $\\prod_{i=0}^{n-1} 2 = 2^n$.

**Product vs. sum comparison**:

| Sum pattern | Product pattern |
|-------------|-----------------|
| `sum_range_zero` (gives 0) | `prod_range_zero` (gives 1) |
| `sum_range_succ` (peels last + term) | `prod_range_succ` (peels last * factor) |
| Close with `ring` or `omega` | Close with `ring` or `omega` |

The identity elements are different (0 vs. 1), but the inductive
structure is identical. In the next levels, you'll use these product
tools to connect a product to the factorial.
"

NewTheorem Finset.prod_range_zero Finset.prod_range_succ

/-- Disabled: directly gives `b ^ n = ∏ k ∈ range n, b`. -/
TheoremDoc Finset.pow_eq_prod_const as "Finset.pow_eq_prod_const" in "BigOp"
/-- Disabled: directly gives `∏ x ∈ s, b = b ^ #s`. -/
TheoremDoc Finset.prod_const as "Finset.prod_const" in "BigOp"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.prod_mul_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub Finset.pow_eq_prod_const Finset.prod_const Finset.sum_range_id_mul_two Finset.sum_range_id
