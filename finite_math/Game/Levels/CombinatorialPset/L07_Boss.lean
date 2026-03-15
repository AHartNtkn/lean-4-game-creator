import GameServer.Commands
import Mathlib

World "CombinatorialPset"
Level 7

Title "Boss: a standalone combinatorial identity"

Introduction
"
# Boss: Derive a binomial identity by specialization

Prove the following identity:

$$\\sum_{k=0}^{n} 3^k \\cdot \\binom{n}{k} = 4^n$$

## Strategy

This comes from setting $x = 3$ and $y = 1$ in the binomial theorem:

$$(3 + 1)^n = \\sum_{k=0}^{n} 3^k \\cdot 1^{n-k} \\cdot \\binom{n}{k}$$

Since $1^{n-k} = 1$, each term simplifies to $3^k \\cdot \\binom{n}{k}$.
And $(3 + 1)^n = 4^n$.

## Proof plan

1. Apply `add_pow` with `x = 3, y = 1` to get `h : (3 + 1) ^ n = ∑ ...`
2. Simplify `(3 + 1)` to `4` — but these are definitionally equal in `ℕ`
3. Simplify `1 ^ (n - m)` to `1` using `one_pow`
4. Simplify `... * 1` to `...` using `mul_one`

## Concrete check

For $n = 2$:
$$3^0 \\cdot 1 + 3^1 \\cdot 2 + 3^2 \\cdot 1 = 1 + 6 + 9 = 16 = 4^2 \\quad ✓$$
"

/-- ∑ 3^k * C(n, k) = 4^n, derived from the binomial theorem. -/
Statement (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), 3 ^ k * Nat.choose n k = 4 ^ n := by
  Hint (hidden := true) "**Step 1**: Apply the binomial theorem with `x = 3, y = 1`.

  Try `have h := add_pow (3 : ℕ) 1 n`."
  have h := add_pow (3 : ℕ) 1 n
  Hint (hidden := true) "Good! Now `h` contains `↑(Nat.choose n m)` with a cast.
  Use `push_cast at h` to normalize the cast away (it's ℕ → ℕ, so trivial)."
  push_cast at h
  Hint (hidden := true) "**Step 2**: Each term has a factor `1 ^ (n - m)` which equals `1`.
  Simplify using `Finset.sum_congr`:

  ```
  have key : ∀ m ∈ Finset.range (n + 1),
      3 ^ m * 1 ^ (n - m) * Nat.choose n m = 3 ^ m * Nat.choose n m := by
    intro m _; rw [one_pow, mul_one]
  rw [Finset.sum_congr rfl key] at h
  ```"
  have key : ∀ m ∈ Finset.range (n + 1),
      3 ^ m * 1 ^ (n - m) * Nat.choose n m = 3 ^ m * Nat.choose n m := by
    intro m _; rw [one_pow, mul_one]
  rw [Finset.sum_congr rfl key] at h
  Hint (hidden := true) "**Step 3**: Now `h : (3 + 1) ^ n = ∑ ...` and the goal
  is `∑ ... = 4 ^ n`. Since `3 + 1 = 4` definitionally, use `exact h.symm`."
  exact h.symm

Conclusion
"
Congratulations on completing the **Combinatorial Identity Transfer**
problem set!

You proved $\\sum_{k=0}^{n} 3^k \\binom{n}{k} = 4^n$ by:

1. **Applying** `add_pow 3 1 n` to invoke the binomial theorem
2. **Simplifying** $1^{n-k} = 1$ using `one_pow`
3. **Simplifying** $\\ldots \\cdot 1 = \\ldots$ using `mul_one`
4. **Concluding** by `exact h.symm`

## What you retrieved in this world

| Level | Skill | From world |
|-------|-------|-----------|
| L01 | Pascal's rule on a fresh row (M28) | W18 |
| L02 | Symmetry on a fresh pair (M30) | W18 |
| L03 | Vandermonde on fresh values (M31) | W19 |
| L04 | Binomial theorem specialization (M29) | W19 |
| L05 | Transfer: combinatorial vs algebraic (T7) | W19 |
| L06 | Transfer: binomial theorem as tool (T7, T10) | W19 |
| L07 | Boss: multi-step specialization | All |

## Transfer moment

On paper, this proof would read:

> *Set $x = 3, y = 1$ in the binomial theorem:*
> $$(3 + 1)^n = \\sum_{k=0}^{n} 3^k \\cdot 1^{n-k} \\cdot \\binom{n}{k} = \\sum_{k=0}^{n} 3^k \\binom{n}{k}$$
> *Since $(3+1)^n = 4^n$, we conclude $4^n = \\sum_{k=0}^{n} 3^k \\binom{n}{k}$. $\\square$*

## The specialization method

You have now used this technique multiple times:

| Substitution | Result |
|-------------|--------|
| $x = y = 1$ | $2^n = \\sum \\binom{n}{k}$ |
| $x = 1, y = -1$ | $0 = \\sum (-1)^k \\binom{n}{k}$ |
| $x = -1, y = 2$ | $1 = \\sum (-1)^k 2^{n-k} \\binom{n}{k}$ |
| $x = 1, y = 2$ | $3^n = \\sum 2^{n-k} \\binom{n}{k}$ |
| $x = 3, y = 1$ | $4^n = \\sum 3^k \\binom{n}{k}$ |

The pattern is clear: every pair $(x, y)$ gives an identity.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
