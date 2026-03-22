import Game.Metadata

World "PascalsTriangle"
Level 11

Title "Convolution: The Sum of Products"

Introduction "
# The Antidiagonal's Canonical Application

You have learned the antidiagonal's API: membership, reindexing,
and swapping. But **why** does the antidiagonal exist?

The answer is **convolution**. A convolution sum has the form:
$$\\sum_{i + j = n} a_i \\cdot b_j$$

This is a sum over **pairs** whose coordinates sum to $n$ — exactly
what `antidiagonal n` provides.

The most famous convolution identity is the **Vandermonde identity**:
$$\\binom{m + n}{k} = \\sum_{(i,j) \\in \\text{antidiagonal}(k)} \\binom{m}{i} \\cdot \\binom{n}{j}$$

In Level 10, you verified this on concrete numbers. Now prove the
specialization $m = n = k = n$:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{i} \\cdot \\binom{n}{j} = \\binom{2n}{n}$$

This is the **sum of products of paired binomial coefficients**.
On the antidiagonal, $i + j = n$, so $\\binom{n}{j} = \\binom{n}{n-i}
= \\binom{n}{i}$ by symmetry — each product is really a square.
"

/-- The sum of products C(n,i)*C(n,j) over the antidiagonal equals C(2n,n). -/
Statement (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
      Nat.choose n p.1 * Nat.choose n p.2 = Nat.choose (2 * n) n := by
  Hint "The Vandermonde identity `Nat.add_choose_eq m n k` says:
  `(m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2`.

  With $m = n$, $k = n$, the RHS matches your LHS. But $2n$ on the
  right side of your goal is written as `2 * n`, while Vandermonde
  gives `(n + n).choose n`. First establish that `2 * n = n + n`.
  This is the reshape-flip-apply pattern again."
  Hint (hidden := true) "Try `have h : 2 * n = n + n := by ring`."
  have h : 2 * n = n + n := by ring
  Hint "Now rewrite the goal to use `n + n` instead of `2 * n`."
  Hint (hidden := true) "Try `rw [h]`."
  rw [h]
  Hint "The goal is now:
  `∑ p ∈ antidiagonal n, choose n p.1 * choose n p.2 = (n + n).choose n`.

  This is exactly the Vandermonde identity `Nat.add_choose_eq n n n`
  read backwards. Use `symm` to flip the equation."
  Hint (hidden := true) "Try `symm`."
  symm
  Hint "Now the goal is `(n + n).choose n = ∑ p ∈ antidiagonal n, ...`.
  Apply `Nat.add_choose_eq` directly."
  Hint (hidden := true) "Try `exact Nat.add_choose_eq n n n`."
  exact Nat.add_choose_eq n n n

Conclusion "
You proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{i} \\cdot \\binom{n}{j} = \\binom{2n}{n}$$

**Why this matters**: This is the first **multiplicative** sum over
the antidiagonal you have computed. The additive sums in Levels 7-8
($\\sum \\binom{n}{i}$ and $\\sum \\binom{n}{j}$) could have been
written as range sums. But this convolution sum
$\\sum_{i+j=n} a_i \\cdot b_j$ is **naturally** an antidiagonal sum —
the product structure makes the pair indexing essential.

**The central binomial coefficient $\\binom{2n}{n}$**: This is one of
the most important sequences in combinatorics. It counts the number of
lattice paths from $(0,0)$ to $(n,n)$, and is the largest entry in
row $2n$ of Pascal's triangle.

**Polynomial multiplication connection**: In the Products world (W24),
you will see that multiplying two polynomials $f$ and $g$ produces
coefficients $(fg)_n = \\sum_{i+j=n} f_i \\cdot g_j$ — exactly this
antidiagonal convolution.

**Concrete check**: For $n = 3$:
$$1 \\cdot 1 + 3 \\cdot 3 + 3 \\cdot 3 + 1 \\cdot 1 = 1 + 9 + 9 + 1 = 20 = \\binom{6}{3}$$
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
