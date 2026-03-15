import GameServer.Commands
import Mathlib

World "Factorials"
Level 7

Title "Boss: Factorial equals product"

Introduction
"
# Boss: $n! = \\prod_{i=0}^{n-1}(i+1)$

Time to integrate everything from this world.

## The statement

Prove by induction that $n! = \\prod_{i=0}^{n-1}(i+1)$, connecting
the recursive definition of factorial to the big-product formula.

## Strategy

This proof requires four skills you have practiced:

1. **Induction** on `n` (from many earlier worlds)
2. **`Nat.factorial_succ`** (L01–L02): unfold the factorial
3. **`Finset.prod_range_succ`** (W15): peel off the last factor from
   the product
4. **`mul_comm`** (basic algebra): swap the order of multiplication

### Base case

When $n = 0$: $0! = 1$ and $\\prod_{i \\in \\emptyset}(i+1) = 1$.
Both sides are `1`.

### Inductive step

Assume $n! = \\prod_{i=0}^{n-1}(i+1)$. Then:

$$(n+1)! = (n+1) \\cdot n! = (n+1) \\cdot \\prod_{i=0}^{n-1}(i+1)$$

And:

$$\\prod_{i=0}^{n}(i+1) = \\left(\\prod_{i=0}^{n-1}(i+1)\\right) \\cdot (n+1)$$

These are equal by commutativity of multiplication.
"

/-- Factorial equals the product of 1 through n. -/
Statement (n : ℕ) : Nat.factorial n = ∏ i ∈ Finset.range n, (i + 1) := by
  Hint "Start with `induction n with` to prove this by induction on `n`."
  induction n with
  | zero =>
    Hint "In the base case, `0! = 1` and the product over `range 0 = ∅` is `1`.

    Use `rw [Nat.factorial_zero, Finset.prod_range_zero]`."
    Hint (hidden := true) "Try `rw [Nat.factorial_zero, Finset.prod_range_zero]`."
    rw [Nat.factorial_zero, Finset.prod_range_zero]
  | succ n ih =>
    Hint "In the inductive step, you need to connect:
    - `(n + 1).factorial` on the left
    - `∏ i ∈ range (n + 1), (i + 1)` on the right

    Start by unfolding the factorial: `rw [Nat.factorial_succ]`.
    This gives `(n + 1) * n.factorial = ∏ i ∈ range (n + 1), (i + 1)`."
    Hint (hidden := true) "Try `rw [Nat.factorial_succ]`."
    rw [Nat.factorial_succ]
    Hint "Now apply the inductive hypothesis to replace `n.factorial`
    with `∏ i ∈ range n, (i + 1)`:

    `rw [ih]`"
    Hint (hidden := true) "Try `rw [ih]`."
    rw [ih]
    Hint "The goal is now:
    ```
    (n + 1) * ∏ i ∈ range n, (i + 1) = ∏ i ∈ range (n + 1), (i + 1)
    ```

    Use `rw [Finset.prod_range_succ]` to peel off the last factor from
    the right-hand product."
    Hint (hidden := true) "Try `rw [Finset.prod_range_succ]`."
    rw [Finset.prod_range_succ]
    Hint "The goal is now:
    ```
    (n + 1) * ∏ i ∈ range n, (i + 1) = (∏ i ∈ range n, (i + 1)) * (n + 1)
    ```

    These differ only in the order of multiplication.
    Use `mul_comm` to close it."
    Hint (hidden := true) "Try `rw [mul_comm]`."
    rw [mul_comm]

Conclusion
"
Congratulations on completing the **Factorials** world!

You proved the general identity:

$$n! = \\prod_{i=0}^{n-1}(i+1) = 1 \\cdot 2 \\cdot 3 \\cdots n$$

## The proof structure

- **Base**: $0! = 1 = \\prod_{\\emptyset}(i+1)$
- **Step**: $(n+1)! = (n+1) \\cdot n! = (n+1) \\cdot \\prod_{i<n}(i+1) = \\prod_{i<n+1}(i+1)$

Each rewrite step used a single lemma:
1. `factorial_succ` — unfolded $(n+1)!$
2. `ih` — applied the inductive hypothesis
3. `prod_range_succ` — peeled off the last factor $(n+1)$
4. `mul_comm` — reordered the multiplication

## What you learned in this world

- **L01**: `Nat.factorial` definition and `factorial_succ` / `factorial_zero`
- **L02**: Factorial recursion as an algebraic identity
- **L03**: Factorial as a big product — concrete verification
- **L04**: Descending factorials `Nat.descFactorial` and their recursion
- **L05**: Key identity $n^{\\underline{n}} = n!$ by induction
- **L06**: Counting permutations: $|\\mathrm{Perm}(\\mathrm{Fin}\\;n)| = n!$
- **L07**: Boss — the general identity $n! = \\prod_{i<n}(i+1)$

## Transfer moment

On paper you would write:

> *Proof by induction on $n$.*
> *Base case*: $0! = 1$ and the empty product is $1$. $\\checkmark$
> *Inductive step*: Assume $n! = \\prod_{i=0}^{n-1}(i+1)$. Then
> $(n+1)! = (n+1) \\cdot n! = (n+1) \\prod_{i=0}^{n-1}(i+1)
> = \\prod_{i=0}^{n}(i+1)$. $\\square$

This is a routine induction with one algebraic trick: recognizing
that peeling $(n+1)$ off the factorial matches peeling $(n+1)$ off
the end of the product.

## What comes next

The next world introduces **binomial coefficients** and Pascal's rule.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
