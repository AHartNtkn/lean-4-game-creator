import Game.Metadata

World "PascalsTriangle"
Level 14

Title "Symmetry on the Antidiagonal"

Introduction "
# Binomial Coefficient Symmetry, Pair by Pair

In Level 2, you proved that $\\binom{n+6}{3} = \\binom{n+6}{n+3}$ —
the symmetry of a single row entry. Now apply this symmetry to
**pairs on the antidiagonal**.

For any pair $(p_1, p_2)$ with $p_1 + p_2 = n$, we have
$p_2 = n - p_1$ and $p_1 \\le n$. By `choose_symm`:
$$\\binom{n}{p_2} = \\binom{n}{n - p_1} = \\binom{n}{p_1}$$

So on the antidiagonal, $\\binom{n}{\\text{first}} = \\binom{n}{\\text{second}}$.
This is the key insight you will need in Level 15 to connect
squared coefficients to the Vandermonde convolution.

**Proof plan**:
1. Extract the arithmetic from the membership: `p.1 + p.2 = n`
2. Derive `p.2 = n - p.1` and `p.1 ≤ n`
3. Rewrite and apply `choose_symm`
"

/-- On the antidiagonal, choose n applied to either coordinate gives the same result. -/
Statement (n : ℕ) (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal n) :
    Nat.choose n p.1 = Nat.choose n p.2 := by
  Hint "Extract the arithmetic from the membership hypothesis.
  `Finset.mem_antidiagonal` converts `p ∈ antidiagonal n` to
  `p.1 + p.2 = n`."
  Hint (hidden := true) "Try `rw [Finset.mem_antidiagonal] at hp`."
  rw [Finset.mem_antidiagonal] at hp
  Hint "From `hp : p.1 + p.2 = n`, derive that `p.2 = n - p.1`."
  Hint (hidden := true) "Try `have h_eq : p.2 = n - p.1 := by omega`."
  have h_eq : p.2 = n - p.1 := by omega
  Hint "Also derive `p.1 ≤ n` (needed for `choose_symm`)."
  Hint (hidden := true) "Try `have h_le : p.1 ≤ n := by omega`."
  have h_le : p.1 ≤ n := by omega
  Hint "Rewrite `p.2` to `n - p.1`, then apply `choose_symm`:
  `choose n (n - p.1) = choose n p.1`."
  Hint (hidden := true) "Try `rw [h_eq, Nat.choose_symm h_le]`."
  rw [h_eq, Nat.choose_symm h_le]

Conclusion "
For any $(p_1, p_2)$ with $p_1 + p_2 = n$:
$$\\binom{n}{p_1} = \\binom{n}{p_2}$$

This is the **term-by-term symmetry** of the antidiagonal: the
two coordinates of any pair give the same binomial coefficient.

**The antidiagonal constraint is essential**: Without the
hypothesis $p_1 + p_2 = n$, symmetry fails. For instance,
$\\binom{4}{1} = 4 \\neq 6 = \\binom{4}{2}$ for the pair $(1, 2)$,
which lies on antidiagonal $3$, not antidiagonal $4$. The
constraint $i + j = n$ is what makes $j = n - i$, which is what
makes `choose_symm` applicable.

**Two views of the same symmetry**: Level 2 used `choose_symm`
on a single entry (position 3 vs position $n+3$ in a row).
This level uses `choose_symm` on antidiagonal pairs. The next
level will use this to connect squared coefficients to the
Vandermonde product sum.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add
