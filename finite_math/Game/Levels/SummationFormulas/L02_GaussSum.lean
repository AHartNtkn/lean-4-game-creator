import Game.Metadata

World "SummationFormulas"
Level 2

Title "The Gauss Sum"

Introduction "
# The Sum of the First $n$ Natural Numbers

The most famous summation formula is the **Gauss sum**:

$$\\sum_{i=0}^{n} i = \\frac{n(n+1)}{2}$$

Legend has it that the young Carl Friedrich Gauss, asked to sum
$1 + 2 + \\cdots + 100$ as a schoolboy, immediately answered $5050$.
His trick: pair each number with its 'mirror': $1 + 100 = 2 + 99
= \\cdots = 101$. With $50$ such pairs, the total is $50 \\times 101 = 5050$.
This **pairing argument** is one of the most celebrated insights
in elementary mathematics.

Since division on natural numbers is floor division (and we don't
want to deal with that), we state this as:

$$2 \\cdot \\sum_{i=0}^{n} i = n \\cdot (n+1)$$

**The proof plan**:
- **Base case**: $2 \\cdot \\sum_{i \\in \\text{range } 1} i = 0 \\cdot 1 = 0$.
  You'll peel `range 1` with `sum_range_succ`, then simplify
  `range 0` with `sum_range_zero`, and close with `ring`.

- **Inductive step**: Peel `range (n+2)` with `sum_range_succ`, then
  distribute the $2$ with `mul_add`, substitute the IH, and close
  with `ring`.

**New tool**: `mul_add` distributes multiplication over addition:

```
mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c
```

You need `mul_add` because after peeling, the goal has the shape
$2 \\cdot (\\Sigma + k)$, and you need to separate $2 \\cdot \\Sigma$
(which the IH knows about) from $2 \\cdot k$.
"

/-- `mul_add` states that `a * (b + c) = a * b + a * c`.

Distributes multiplication over addition (left distributivity).

## Syntax
```
rw [mul_add]
```

## When to use it
When you see `a * (b + c)` in the goal and need to separate
the two summands. This is useful in inductive steps where the
sum gets peeled and you need to isolate the part that matches
the induction hypothesis.

## Example
```
-- Goal: 2 * (∑ x + k) = ...
rw [mul_add]
-- Goal: 2 * ∑ x + 2 * k = ...
-- Now rw [ih] can substitute 2 * ∑ x
```
-/
TheoremDoc mul_add as "mul_add" in "Algebra"

/-- Disabled: directly gives `(∑ i ∈ range n, i) * 2 = n * (n - 1)`. -/
TheoremDoc Finset.sum_range_id_mul_two as "Finset.sum_range_id_mul_two" in "BigOp"
/-- Disabled: directly gives `∑ i ∈ range n, i = n * (n - 1) / 2`. -/
TheoremDoc Finset.sum_range_id as "Finset.sum_range_id" in "BigOp"

/-- The Gauss sum: twice the sum of 0..n equals n times (n+1). -/
Statement (n : ℕ) : 2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by
  Hint "Induct on `n` using natural number induction."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: Simplify `range 1`.
    Use `sum_range_succ` to peel off the last term, then
    `sum_range_zero` to clear `range 0`."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Finset.sum_range_zero]`
    then `ring`."
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    Hint "The goal is `2 * (0 + 0) = 0 * (0 + 1)`. Close with `ring`."
    Hint (hidden := true) "Try `ring`."
    ring
  | succ n ih =>
    Hint "**Inductive step**: First, peel off the last term with
    `sum_range_succ`. Then distribute the $2$ with `mul_add` to
    separate the sum from the last term. Finally, substitute
    the IH and close with `ring`."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, mul_add, ih]`
    then `ring`."
    rw [Finset.sum_range_succ]
    Hint (hidden := true) "The IH is about `2 * ∑`, but the goal has
    `2 * (∑ + ...)`. You need `mul_add` to distribute the $2$ first,
    so the IH's pattern becomes visible.

    Try `rw [mul_add, ih]` then `ring`."
    rw [mul_add, ih]
    Hint "After peeling and distributing:
    - `sum_range_succ` turned `range (n+2)` into `(∑ range (n+1)) + (n+1)`
    - `mul_add` turned `2 * (∑ + (n+1))` into `2*∑ + 2*(n+1)`
    - `ih` turned `2 * ∑` into `n*(n+1)`

    The goal is now `n*(n+1) + 2*(n+1) = (n+1)*(n+2)`. `ring` closes it."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
You proved the Gauss sum formula:
$$2\\sum_{i=0}^{n} i = n(n+1)$$

**Why multiply by 2?** The standard formula is
$\\sum_{i=1}^{n} i = \\frac{n(n+1)}{2}$. In natural numbers, division
is floor division: $5 / 2 = 2$, not $2.5$. If $n(n+1)$ happened to
be odd (it can't, but Lean doesn't know that without proof), dividing
by 2 would lose information. Multiplying both sides by 2 eliminates
the division entirely, giving an identity that's unconditionally true
over $\\mathbb{N}$. This is a common formalization technique: avoid
division by restating the equation multiplicatively.

**The Gauss pairing argument**: Your induction proof is correct but
hides the *reason* the formula is $n(n+1)/2$. Here is the intuitive
argument: write the sum twice, once forward and once backward:

$$S = 0 + 1 + 2 + \\cdots + (n-1) + n$$
$$S = n + (n-1) + (n-2) + \\cdots + 1 + 0$$

Adding term-by-term: each pair sums to $n$, and there are $n+1$
pairs, so $2S = n(n+1)$. This is the **fold-and-add** or
**pairing** argument. The factor of 2 in our statement comes
directly from writing the sum twice.

In Lean, this pairing can be expressed via `Finset.sum_range_reflect`,
which reverses the indexing of a sum. The algebraic proof you wrote
captures the same content through induction — both approaches
ultimately rely on the symmetry $i + (n - i) = n$.

**Key move**: `mul_add` distributes `2 * (∑ + k)` into `2*∑ + 2*k`,
letting you isolate `2*∑` for the IH. Without this step, `ring`
can't see where to apply the IH because it's buried inside a product.

**The inductive step pattern for this world**:
1. `rw [sum_range_succ]` — peel
2. Additional rewrites if needed (`mul_add`, `add_assoc`, etc.)
3. `rw [ih]` — substitute the IH
4. `ring` — close the algebra
"

NewTheorem mul_add

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.pow_eq_prod_const Finset.prod_const
