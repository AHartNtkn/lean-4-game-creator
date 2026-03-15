import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 9

Title "Boss: C(n, 1) = n by induction"

Introduction
"
# Boss: Prove $\\binom{n}{1} = n$ by induction

In L07, you used `Nat.choose_one_right` as a library lemma.
Now prove it yourself from first principles — using only the
recursive definition (Pascal's rule and boundary conditions).

## Strategy

**Induction on $n$.**

### Base case ($n = 0$):

$\\binom{0}{1} = 0$ because $1 = 0 + 1$ and `choose_zero_succ` gives
$\\binom{0}{k+1} = 0$.

### Inductive step:

Assume $\\binom{n}{1} = n$. Prove $\\binom{n+1}{1} = n+1$.

Apply Pascal's rule with $k = 0$:

$$\\binom{n+1}{1} = \\binom{n}{0} + \\binom{n}{1} = 1 + n = n + 1$$

This uses:
1. `Nat.choose_succ_succ` — Pascal's rule
2. `Nat.choose_zero_right` — $\\binom{n}{0} = 1$
3. The inductive hypothesis — $\\binom{n}{1} = n$
4. `add_comm` — $1 + n = n + 1$

## Tools you need

- `induction n with` — start the induction
- `Nat.choose_succ_succ` — Pascal's rule
- `Nat.choose_zero_right` — boundary: $\\binom{n}{0} = 1$
- `Nat.choose_zero_succ` — boundary: $\\binom{0}{k+1} = 0$
- `add_comm` — commutativity of addition
- `rw [ih]` — apply the inductive hypothesis
"

/-- C(n, 1) = n, proved by induction using Pascal's rule. -/
Statement (n : ℕ) : Nat.choose n 1 = n := by
  Hint "Start with `induction n with` to set up the induction."
  induction n with
  | zero =>
    Hint "**Base case**: prove `Nat.choose 0 1 = 0`.

    Since `1 = 0 + 1`, you can use `Nat.choose_zero_succ` which says
    `Nat.choose 0 (k + 1) = 0`.

    Try `rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]`."
    Hint (hidden := true) "Try
    `rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]`."
    rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]
  | succ n ih =>
    Hint "**Inductive step**: prove `Nat.choose (n + 1) 1 = n + 1`,
    given `ih : Nat.choose n 1 = n`.

    Start by applying Pascal's rule. Since `1 = 0 + 1`, the lemma
    `Nat.choose_succ_succ` applies with `k = 0`:

    `choose (n+1) 1 = choose n 0 + choose n 1`

    Try `rw [Nat.choose_succ_succ]`."
    Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
    rw [Nat.choose_succ_succ]
    Hint "Good! The goal is now
    `Nat.choose n 0 + Nat.choose n 1 = n + 1`.

    Use `Nat.choose_zero_right` to simplify the first term to `1`."
    Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
    rw [Nat.choose_zero_right]
    Hint "The goal is `1 + Nat.choose n 1 = n + 1`.

    Apply the inductive hypothesis: `rw [ih]` replaces
    `Nat.choose n 1` with `n`."
    Hint (hidden := true) "Try `rw [ih]`."
    rw [ih]
    Hint "The goal is `1 + n = n + 1`.

    These are equal by commutativity of addition. Use `add_comm`."
    Hint (hidden := true) "Try `rw [add_comm]`."
    rw [add_comm]

Conclusion
"
Congratulations on completing the **Binomial Coefficients** world!

You proved $\\binom{n}{1} = n$ from first principles — no library lemma,
just the recursive definition.

## The proof structure

- **Base**: $\\binom{0}{1} = 0$ by `choose_zero_succ`
- **Step**: $\\binom{n+1}{1} = \\binom{n}{0} + \\binom{n}{1} = 1 + n = n + 1$

Each rewrite step used a single lemma:
1. `choose_succ_succ` — applied Pascal's rule with $k = 0$
2. `choose_zero_right` — simplified $\\binom{n}{0} = 1$
3. `ih` — applied the inductive hypothesis
4. `add_comm` — rearranged $1 + n = n + 1$

## What you learned in this world

- **L01**: `Nat.choose` definition and recursive computation
- **L02**: Boundary values: `choose_zero_right`, `choose_self`, `choose_zero_succ`
- **L03**: `choose n k = 0` when $k > n$ (C10 misconception)
- **L04**: Pascal's rule: `choose_succ_succ`
- **L05**: Pascal's rule applied to compute specific values
- **L06**: Symmetry: `choose_symm`
- **L07**: Combinatorial interpretation: `choose_one_right`
- **L08**: Row sum: $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$
- **L09**: Boss — `choose n 1 = n` by induction

## Transfer moment

On paper you would write:

> *Proof by induction on $n$.*
> *Base case*: $\\binom{0}{1} = 0$. ✓
> *Inductive step*: Assume $\\binom{n}{1} = n$. Then by Pascal's rule,
> $\\binom{n+1}{1} = \\binom{n}{0} + \\binom{n}{1} = 1 + n = n + 1$. $\\square$

This is a clean induction: Pascal's rule decomposes the coefficient,
the boundary condition and inductive hypothesis simplify, and
commutativity finishes.

## What comes next

The next world explores **Pascal's triangle row by row** with
concrete computations, then the course moves on to the **binomial
theorem** and further identities.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
DisabledTheorem Nat.choose_one_right
