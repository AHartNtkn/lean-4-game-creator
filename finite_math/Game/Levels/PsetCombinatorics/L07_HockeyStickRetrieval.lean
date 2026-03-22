import Game.Metadata

World "PsetCombinatorics"
Level 7

Title "Hockey Stick Retrieval"

Introduction "
# The Hockey Stick for $k = 2$

In BinomialCoefficients (Level 15), you proved the **hockey stick
identity** by induction:

$$\\sum_{i=0}^{n} \\binom{i}{k} = \\binom{n+1}{k+1}$$

The proof technique was:
- **Base case**: simplify the single-term sum, show both sides
  are zero using `choose_eq_zero_of_lt`
- **Inductive step**: peel off the last term with `sum_range_succ`,
  substitute the IH, commute, and fold with `← choose_succ_succ`

Now re-derive the $k = 2$ case:

$$\\sum_{i=0}^{n} \\binom{i}{2} = \\binom{n+1}{3}$$

This is the identity $0 + 0 + 1 + 3 + 6 + 10 + \\cdots = \\binom{n+1}{3}$:
summing triangular numbers gives a tetrahedral number.

**Strategy**: Induction on $n$, following the Level 15 pattern.
"

/-- The hockey stick identity for k = 2. -/
Statement (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Nat.choose i 2 = Nat.choose (n + 1) 3 := by
  Hint "Use **induction** on `n`."
  Hint (hidden := true) "Type `induction n`."
  induction n with
  | zero =>
    Hint "**Base case** (n = 0): The sum has one term at $i = 0$.
    Simplify the sum structure first: peel the single term and
    remove the empty sum."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]`."
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    Hint "The goal is `choose 0 2 = choose 1 3`. Both sides are
    zero because $0 < 2$ and $1 < 3$. Use `Nat.choose_eq_zero_of_lt`
    with explicit proofs."
    Hint (hidden := true) "Try `rw [Nat.choose_eq_zero_of_lt (by omega : 0 < 2), Nat.choose_eq_zero_of_lt (by omega : 1 < 3)]`."
    rw [Nat.choose_eq_zero_of_lt (by omega : 0 < 2),
        Nat.choose_eq_zero_of_lt (by omega : 1 < 3)]
  | succ n ih =>
    Hint "**Inductive step**: Peel the last term, substitute the IH,
    commute, and fold with backward Pascal."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ]`."
    rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ]

Conclusion "
The same induction pattern from BinomialCoefficients Level 15:
peel, substitute, commute, fold. The sum
$0 + 0 + 1 + 3 + 6 + 10 + \\cdots$ of triangular numbers gives
the tetrahedral number $\\binom{n+1}{3}$.

Notice that the inductive step — `add_comm` then
`← choose_succ_succ` — is exactly the backward Pascal fold from
Level 1. The hockey stick identity can be read as a
**telescoping sum**: each application of backward Pascal collapses
one term, and iterating this across the entire sum gives the
hockey stick. Induction formalizes this telescoping argument.

**Row sum vs column sum**: Compare this with the row sum identity
$\\sum_k C(n, k) = 2^n$ from BinomialTheorem. The row sum fixes
$n$ and sums over $k$ (across a row of Pascal's triangle). The
hockey stick fixes $k$ and sums over $i$ (down a diagonal). Both
are sums of binomial coefficients, but they sum in different
directions — confusing which index varies is a common mistake.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
