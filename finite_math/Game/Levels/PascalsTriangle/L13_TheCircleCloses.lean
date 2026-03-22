import Game.Metadata

World "PascalsTriangle"
Level 13

Title "The Circle Closes"

Introduction "
# Pascal's Recurrence from Vandermonde

In Level 1, you used Pascal's identity (`choose_succ_succ`) as a
**given tool** to walk down the triangle. In Level 12, you proved
that the Vandermonde specialization $m = 1$ gives:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(k)} \\binom{1}{i} \\cdot \\binom{n}{j} = \\binom{n+1}{k}$$

Now **close the circle**: show that this Vandermonde sum, for
$k + 1$, equals exactly the two terms of Pascal's recurrence:
$$\\binom{n}{k} + \\binom{n}{k+1}$$

**Why only two terms?** The antidiagonal of $k + 1$ contains
pairs $(0, k+1), (1, k), (2, k-1), \\ldots$ But $\\binom{1}{i} = 0$
for $i \\ge 2$, so only the first two terms survive:
- $(0, k+1)$: $\\binom{1}{0} \\cdot \\binom{n}{k+1} = \\binom{n}{k+1}$
- $(1, k)$: $\\binom{1}{1} \\cdot \\binom{n}{k} = \\binom{n}{k}$

The sum is $\\binom{n}{k} + \\binom{n}{k+1} = \\binom{n+1}{k+1}$.
This IS Pascal's identity — the defining recurrence of the triangle
is a consequence of Vandermonde.

**Proof plan**:
1. Use Vandermonde ($m = 1$) to show the sum equals $\\binom{n+1}{k+1}$
   (the reshape-flip-apply pattern from Level 12)
2. Apply `choose_succ_succ` to expand $\\binom{n+1}{k+1}$
"

/-- The Vandermonde m=1 sum equals Pascal's recurrence terms. -/
Statement (n k : ℕ) :
    ∑ p ∈ Finset.antidiagonal (k + 1),
      Nat.choose 1 p.1 * Nat.choose n p.2 =
    Nat.choose n k + Nat.choose n (k + 1) := by
  Hint "The Vandermonde identity with $m = 1$ gives:
  `(1 + n).choose (k+1) = ∑ p ∈ antidiagonal (k+1), choose 1 p.1 * choose n p.2`.

  First use this to show the LHS equals `choose (n+1) (k+1)`.
  You need `n + 1 = 1 + n` to match Vandermonde's form."
  Hint (hidden := true) "Try
  `have h_vand : ∑ p ∈ Finset.antidiagonal (k + 1), Nat.choose 1 p.1 * Nat.choose n p.2 = Nat.choose (n + 1) (k + 1) := by`
  then inside: `have hh : n + 1 = 1 + n := by ring`
  then `rw [hh]`, `symm`, `exact Nat.add_choose_eq 1 n (k + 1)`."
  have h_vand : ∑ p ∈ Finset.antidiagonal (k + 1), Nat.choose 1 p.1 * Nat.choose n p.2 = Nat.choose (n + 1) (k + 1) := by
    have hh : n + 1 = 1 + n := by ring
    rw [hh]
    symm
    exact Nat.add_choose_eq 1 n (k + 1)
  Hint "Good — the sum equals `choose (n+1) (k+1)`.
  Now apply Pascal's identity `choose_succ_succ` to expand
  `choose (n+1) (k+1) = choose n k + choose n (k+1)`."
  Hint (hidden := true) "Try `rw [h_vand]` then `exact Nat.choose_succ_succ n k`."
  rw [h_vand]
  exact Nat.choose_succ_succ n k

Conclusion "
You proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(k+1)} \\binom{1}{i} \\cdot \\binom{n}{j} = \\binom{n}{k} + \\binom{n}{k+1}$$

**The circle is closed.** The world began with Pascal's identity
as a computational tool (Level 1: expand entries by walking down
the triangle). You then built the antidiagonal machinery, proved
Vandermonde, and specialized to $m = 1$ (Level 12). Now you have
shown that Vandermonde with $m = 1$ gives back Pascal's identity.

The starting point is a special case of the climax. The recurrence
that **defines** the triangle is a **consequence** of the
convolution theorem that the triangle satisfies.

**What we did NOT prove here**: We used `choose_succ_succ` as
a library fact to verify the match. A fully self-contained
derivation would expand the antidiagonal sum term by term, showing
that only $(0, k+1)$ and $(1, k)$ contribute. That expansion is
more complex, but the key insight is the same: $\\binom{1}{i} = 0$
for $i \\ge 2$ kills all but two terms.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
