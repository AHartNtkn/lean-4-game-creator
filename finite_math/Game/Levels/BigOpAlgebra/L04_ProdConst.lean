import Game.Metadata

World "BigOpAlgebra"
Level 4

Title "Constant Products: The Multiplicative Twin"

Introduction "
# Constant Products: ∏ c = c ^ card

In the last level, you learned `sum_const`:
$$\\sum_{x \\in s} c = |s| \\cdot c$$

Now meet its **multiplicative twin**. What happens when you
multiply the same value over every element?

$$\\prod_{x \\in s} c = c^{|s|}$$

Each of the `|s|` elements contributes a factor of `c`, so the
product is `c` raised to the power `|s|`. In Lean:

```
Finset.prod_const (c : M) : ∏ x ∈ s, c = c ^ s.card
```

**Connection to sum_const**: The duality table continues:

| Additive | Multiplicative |
|----------|---------------|
| `∑(f + g) = ∑f + ∑g` | `∏(f · g) = ∏f · ∏g` |
| `∑ c = card • c` | `∏ c = c ^ card` |

**Your task**: Split `∏(f · 2)` using `prod_mul_distrib`, then
simplify the constant part with `prod_const`.
"

/-- Combine prod_mul_distrib and prod_const. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∏ x ∈ s, f x = 60) :
    ∏ x ∈ s, (f x * 2) = 60 * 2 ^ s.card := by
  Hint "First split the product `f x * 2` into two products using
  `rw [Finset.prod_mul_distrib]`."
  rw [Finset.prod_mul_distrib]
  Hint "The goal now has `∏ x ∈ s, 2` — a constant product. Use
  `rw [Finset.prod_const]` to convert it to `2 ^ s.card`."
  Hint (hidden := true) "Try `rw [Finset.prod_const]`."
  rw [Finset.prod_const]
  Hint "Now substitute the known product with `rw [hf]`."
  rw [hf]

Conclusion "
You combined two tools:
1. `prod_mul_distrib` split `∏(f · c)` into `∏f · ∏c`
2. `prod_const` simplified `∏c` to `c ^ card`

Notice the parallel with L03:

| Additive | Multiplicative |
|----------|---------------|
| `sum_add_distrib` splits `+` | `prod_mul_distrib` splits `·` |
| `sum_const` gives `card • c` | `prod_const` gives `c ^ card` |

The structural pattern — split, simplify constant part, substitute —
is the same in both cases. Only the operation changes.

**When to use it**: Whenever the factor in a product doesn't depend
on the variable — every element contributes the same factor.
"

/-- `Finset.prod_const` states that `∏ x ∈ s, c = c ^ s.card`.

The product of a constant function equals the constant raised to
the cardinality.

## Syntax
```
exact Finset.prod_const c   -- explicit argument needed
rw [Finset.prod_const]      -- Lean infers c from goal
```

## When to use it
When the factor in a product doesn't depend on the variable —
every element contributes the same factor `c`.

## Connection
This is the multiplicative twin of `Finset.sum_const`
(`∑ x ∈ s, c = s.card • c`).
-/
TheoremDoc Finset.prod_const as "Finset.prod_const" in "BigOp"

NewTheorem Finset.prod_const

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
