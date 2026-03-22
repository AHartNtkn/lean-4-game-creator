import Game.Metadata

World "BinomialCoefficients"
Level 16

Title "Boss: The Triangular Choose"

Introduction "
# Boss: The Triangular Number Formula

The second column of Pascal's triangle gives the **triangular numbers**:

$$\\binom{2}{2} = 1, \\quad \\binom{3}{2} = 3, \\quad \\binom{4}{2} = 6, \\quad \\binom{5}{2} = 10, \\ldots$$

Prove the closed-form identity:

$$2 \\cdot \\binom{n+2}{2} = (n+1)(n+2)$$

This is the multiplicative version of the well-known formula
$\\binom{n}{2} = n(n-1)/2$, shifted to avoid natural number subtraction.

**What you need** (all from this world and prior worlds):
- Natural number induction (`induction n with`)
- `Nat.choose_self` — boundary value C(2, 2) = 1 (Level 1)
- `Nat.choose_succ_succ` — Pascal's identity (Level 3)
- `Nat.choose_one_right` — reducing C(n, 1) to n (Level 2)
- `mul_add` — distributing multiplication over addition (from BigOpAlgebra: `a * (b + c) = a * b + a * c`)
- Induction hypothesis — substituting the IH
- `ring` — closing the final polynomial identity

**Proof plan**:
- **Base case** ($n = 0$): C(2, 2) = 1 by `choose_self`, then the
  arithmetic closes automatically.
- **Inductive step**: Expand C(n+3, 2) with Pascal's identity, simplify
  C(n+2, 1) = n+2, distribute the factor of 2, substitute the IH,
  then close with `ring`.
"

/-- 2 * C(n+2, 2) = (n+1) * (n+2). -/
Statement (n : ℕ) : 2 * Nat.choose (n + 2) 2 = (n + 1) * (n + 2) := by
  Hint "This requires **induction** on `n`.
  The base case uses a boundary value; the inductive step uses
  Pascal's identity and the IH."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case** (n = 0): The goal is
    `2 * Nat.choose 2 2 = 1 * 2`.
    Since C(2, 2) = 1, rewrite with `Nat.choose_self`.

    After the rewrite, the goal `2 * 1 = 1 * 2` closes
    automatically — both sides reduce to 2. Don't be surprised
    when the goal disappears!"
    Hint (hidden := true) "Try `rw [Nat.choose_self]`. The goal closes automatically after the rewrite."
    rw [Nat.choose_self]
  | succ n ih =>
    Hint "**Inductive step**: The goal is
    `2 * Nat.choose (n + 3) 2 = (n + 2) * (n + 3)`.

    Strategy:
    1. Expand C(n+3, 2) with Pascal's identity
    2. Simplify C(n+2, 1) to n + 2
    3. Distribute the 2 with `mul_add`
    4. Substitute the induction hypothesis
    5. Close with `ring`"
    Hint (hidden := true) "Start with
    `rw [Nat.choose_succ_succ, Nat.choose_one_right]`."
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    Hint "Good — the goal is
    `2 * ((n + 2) + Nat.choose (n + 2) 2) = (n + 2) * (n + 3)`.

    You need `2 * Nat.choose (n + 2) 2` to appear on its own so
    the IH can rewrite it. Distribute with `mul_add`:
    `mul_add : a * (b + c) = a * b + a * c`."
    Hint (hidden := true) "Try `rw [mul_add, ih]` then `ring`."
    rw [mul_add, ih]
    Hint "The goal is now a pure arithmetic identity involving only
    `n`. Use `ring` to close it."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
Congratulations! You proved:
$$2 \\cdot \\binom{n+2}{2} = (n+1)(n+2)$$

**Skills integrated in this boss**:
1. `induction n with` — natural number induction
2. `Nat.choose_self` — boundary value C(2, 2) = 1 (Level 1)
3. `Nat.choose_succ_succ` — Pascal's identity (Level 3)
4. `Nat.choose_one_right` — C(n, 1) = n (Level 2)
5. `mul_add` — distributing multiplication
6. `ih` — the induction hypothesis
7. `ring` — closing the polynomial identity

**The pattern**: Peel with Pascal, simplify leaves with the boundary
theorems, distribute, substitute the IH, and close with `ring`. This
is the **collect-and-close** skeleton (from FinsetInduction): bring
structural facts into context (here via `rw`), then close with an
algebraic tactic (`ring`). The same skeleton appears in
SummationFormulas, now applied to binomial coefficients.

**The formula**: $\\binom{n}{2} = n(n-1)/2$ counts the number of
2-element subsets — equivalently, the number of handshakes among
$n$ people. These are the **triangular numbers**: $1, 3, 6, 10, 15, \\ldots$

The triangular numbers are also the partial sums $1 + 2 + \\cdots + n =
n(n+1)/2$ from the SummationFormulas world. In Level 14, you proved this
connection formally: $\\sum_{i=0}^{n} i = \\binom{n+1}{2}$. And in Level 15,
you proved the full generalization — the **hockey stick identity**:
$\\sum_{i=0}^{n} \\binom{i}{k} = \\binom{n+1}{k+1}$.

The binomial coefficient $\\binom{n}{2}$ also counts the 2-element
subsets of an $n$-element set — a connection you'll explore in the
**Powerset** world.

The binomial coefficients also give their name to the **binomial theorem**:
$$(x + y)^n = \\sum_{k=0}^{n} \\binom{n}{k}\\, x^k\\, y^{n-k}$$
The entries of row $n$ of Pascal's triangle are exactly the coefficients
in the expansion of $(x+y)^n$ — which is why they are called *binomial*
coefficients. Setting $x = y = 1$ gives $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$:
the sum of each row is a power of $2$. You'll prove this in the
BinomialTheorem world.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases by_cases tauto linarith nlinarith norm_num
DisabledTheorem Nat.choose_two_right Nat.add_one_mul_choose_eq Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
