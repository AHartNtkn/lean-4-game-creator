import Game.Metadata

World "PascalsTriangle"
Level 12

Title "Pascal's Identity from Vandermonde"

Introduction "
# The Punchline: Vandermonde Subsumes Pascal

In Level 1, you used Pascal's identity (choose_succ_succ) as a
given tool to walk down the triangle. In Levels 10-11, you proved
the Vandermonde identity. Now comes the punchline: **Pascal's
identity is a special case of Vandermonde**.

Set $m = 1$ in Vandermonde:
$$\\binom{1 + n}{k} = \\sum_{(i,j) \\in \\text{antidiagonal}(k)} \\binom{1}{i} \\cdot \\binom{n}{j}$$

Since $\\binom{1}{i} = 0$ for $i \\ge 2$, only two terms survive:
$$\\binom{1}{0} \\cdot \\binom{n}{k} + \\binom{1}{1} \\cdot \\binom{n}{k-1}
= \\binom{n}{k} + \\binom{n}{k-1} = \\binom{n+1}{k}$$

This IS Pascal's identity! The defining recurrence of the
triangle is a special case of the convolution theorem.

**Your task**: Prove the Vandermonde specialization $m = 1$.
This uses the same reshape-flip-apply pattern from Level 10.
"

/-- Vandermonde with m=1: the convolution reduces to Pascal's identity. -/
Statement (n k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k,
      Nat.choose 1 p.1 * Nat.choose n p.2 = Nat.choose (n + 1) k := by
  Hint "Vandermonde says `(m + n).choose k = ∑ p ∈ antidiagonal k, m.choose p.1 * n.choose p.2`.
  With $m = 1$, the LHS is `(1 + n).choose k`. Your RHS has `(n + 1).choose k`.
  Reshape: `n + 1 = 1 + n`."
  Hint (hidden := true) "Try `have h : n + 1 = 1 + n := by ring`."
  have h : n + 1 = 1 + n := by ring
  Hint "Rewrite the goal to use `1 + n`."
  Hint (hidden := true) "Try `rw [h]`."
  rw [h]
  Hint "Now flip and apply Vandermonde with `m = 1`."
  Hint (hidden := true) "Try `symm` then `exact Nat.add_choose_eq 1 n k`."
  symm
  exact Nat.add_choose_eq 1 n k

Conclusion "
You proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(k)} \\binom{1}{i} \\cdot \\binom{n}{j} = \\binom{n+1}{k}$$

**Why this matters**: This sum has only two non-zero terms (when
$i = 0$ and $i = 1$, since $\\binom{1}{i} = 0$ for $i \\ge 2$).
So it equals $\\binom{n}{k} + \\binom{n}{k-1} = \\binom{n+1}{k}$.
This is **Pascal's identity** — the defining recurrence of the
triangle.

The world began with Pascal's identity as a tool for computing
entries (Level 1). It ends with the realization that Pascal's
identity is a **consequence** of Vandermonde. The starting point
is a special case of the climax.

**The reshape-flip-apply pattern one more time**: reshape
($n + 1 = 1 + n$), flip (`symm`), apply (`exact add_choose_eq 1 n k`).
This is the fourth time you have used this pattern. It is now a
standard move in your repertoire.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
