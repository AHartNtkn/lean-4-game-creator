import Game.Metadata

World "BinomialCoefficients"
Level 14

Title "Gauss Meets Pascal"

Introduction "
# The Gauss Sum as a Binomial Coefficient

In SummationFormulas, you proved the **Gauss sum formula**:
$0 + 1 + 2 + \\cdots + n = n(n+1)/2$.

Now prove that this same sum equals a **binomial coefficient**:

$$\\sum_{i=0}^{n} i = \\binom{n+1}{2}$$

This is a beautiful **cross-world connection**: a summing question
from SummationFormulas and a counting question from this world give
the same answer. Why? Because $\\binom{n+1}{2}$ counts the 2-element
subsets of an $(n+1)$-element set, and the sum $0 + 1 + \\cdots + n$
counts the same thing by grouping subsets by their larger element.

**Proof strategy**: Induction on $n$.
- **Base case** ($n = 0$): Both sides equal $0$.
- **Inductive step**: Peel the sum, substitute the IH, then show
  $\\binom{n+1}{2} + (n+1) = \\binom{n+2}{2}$ by expanding the right
  side with Pascal's identity and using `choose_one_right`.
"

/-- The Gauss sum equals a binomial coefficient:
∑ i in range (n+1), i = choose (n+1) 2. -/
Statement (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), i = Nat.choose (n + 1) 2 := by
  Hint "Use **induction** on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case** (n = 0): The goal is
    `∑ i in range 1, i = choose 1 2`.

    Simplify the single-term sum (just like Level 13)."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]`."
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    Hint "The goal is `0 = Nat.choose 1 2`.
    Since $1 < 2$, we have `Nat.choose 1 2 = 0` by `choose_eq_zero_of_lt`."
    Hint (hidden := true) "Try `exact (Nat.choose_eq_zero_of_lt (by omega)).symm`."
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ n ih =>
    Hint "**Inductive step**: The goal is
    `∑ i in range (n + 2), i = choose (n + 2) 2`.

    Strategy:
    1. Peel off the last term with `sum_range_succ`
    2. Substitute the IH
    3. Expand `choose (n+2) 2` with Pascal's identity
    4. Simplify `choose (n+1) 1 = n+1`
    5. Close with `omega`"
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]`."
    rw [Finset.sum_range_succ, ih]
    Hint "The goal is `Nat.choose (n + 1) 2 + (n + 1) = Nat.choose (n + 2) 2`.

    Expand the right side: `choose (n+2) 2 = choose (n+1) 1 + choose (n+1) 2`
    by Pascal's identity, then `choose (n+1) 1 = n+1`."
    Hint (hidden := true) "Try:
    `have hp : Nat.choose (n + 2) 2 = Nat.choose (n + 1) 1 + Nat.choose (n + 1) 2 := by rw [Nat.choose_succ_succ]`
    `rw [hp, Nat.choose_one_right]`
    `omega`"
    have hp : Nat.choose (n + 2) 2 = Nat.choose (n + 1) 1 + Nat.choose (n + 1) 2 := by
      rw [Nat.choose_succ_succ]
    rw [hp, Nat.choose_one_right]
    omega

Conclusion "
You proved:
$$\\sum_{i=0}^{n} i = \\binom{n+1}{2}$$

This is a **cross-world connection**: the Gauss sum from
SummationFormulas equals a binomial coefficient. Both count the
same thing — the number of pairs you can form from $n + 1$ elements —
just in different ways:
- The **counting** perspective: $\\binom{n+1}{2}$ directly counts 2-element subsets
- The **summing** perspective: group pairs by the larger element $i$;
  there are $i$ pairs with larger element $i$, so the total is $\\sum_{i=0}^{n} i$

This is an instance of the **hockey stick identity** with $k = 1$
(since $\\binom{i}{1} = i$), which you'll prove in full generality
in the next level.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
