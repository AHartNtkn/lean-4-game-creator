import Game.Metadata

World "SummationFormulas"
Level 11

Title "Factorial as a Product"

Introduction "
# The Factorial as a Product

In the previous level, you computed a specific factorial value using
the recursive definition. Now you'll prove the general connection
between the factorial and big-operator products:

$$n! = \\prod_{i=0}^{n-1} (i + 1) = 1 \\cdot 2 \\cdot 3 \\cdots n$$

**Your task**: Prove this product-to-factorial connection by induction,
using `prod_range_zero`/`prod_range_succ` (from the constant-product level)
and `factorial_zero`/`factorial_succ` (from the previous level).

**Note**: In Level 10, `rfl` was disabled to force you to unfold the
factorial step by step. Here, `rfl` is available again — the base case
$1 = 0!$ is definitionally true, and you've already learned the
recursive structure.
"

/-- The product of (i+1) for i in range n equals n factorial. -/
Statement (n : ℕ) : ∏ i ∈ Finset.range n, (i + 1) = Nat.factorial n := by
  Hint "Induct on `n`. You'll combine product-range tools with
  the factorial recursive definition."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: The product over `range 0` is $1$ (by
    `prod_range_zero`), and $0! = 1$ (by `factorial_zero`).
    So both sides equal $1$."
    Hint (hidden := true) "Try `rw [Finset.prod_range_zero]`."
    rw [Finset.prod_range_zero]
    Hint "The goal is `1 = Nat.factorial 0`. Since `Nat.factorial 0 = 1`
    by definition, `rfl` closes this."
    Hint (hidden := true) "Try `rfl`."
    rfl
  | succ n ih =>
    Hint "**Inductive step**: You need three rewrites:
    1. `Finset.prod_range_succ` — peel off the last factor $(n+1)$
    2. `ih` — substitute the IH ($\\prod = n!$)
    3. `Nat.factorial_succ` — unfold $(n+1)!$ into $(n+1) \\cdot n!$

    Then close with `ring`."
    Hint (hidden := true) "Try
    `rw [Finset.prod_range_succ, ih, Nat.factorial_succ]`
    then `ring`."
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    Hint "After rewriting, both sides are products of `(n+1)` and
    `Nat.factorial n` — just in different order. `ring` handles
    the commutativity."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
You proved that $\\prod_{i=0}^{n-1} (i+1) = n!$, connecting the
big-operator product to the recursively defined factorial.

This is a satisfying bridge between two ways of defining the same thing:
the **recursive** definition (base + step) and the **closed-form**
definition (a single product expression).

The factorial will appear throughout the rest of this course —
in binomial coefficients, counting arguments, and combinatorial
identities.
"

/-- Disabled: directly gives `n! = ∏ i ∈ range n, (i + 1)`. -/
TheoremDoc Nat.factorial_eq_prod_range_add_one as "Nat.factorial_eq_prod_range_add_one" in "Nat"
/-- Disabled: directly gives `∏ i ∈ range n, (i + 1) = n!`. -/
TheoremDoc Finset.prod_range_add_one_eq_factorial as "Finset.prod_range_add_one_eq_factorial" in "BigOp"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.prod_mul_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub Nat.factorial_eq_prod_range_add_one Finset.prod_range_add_one_eq_factorial Finset.sum_range_id_mul_two Finset.sum_range_id
