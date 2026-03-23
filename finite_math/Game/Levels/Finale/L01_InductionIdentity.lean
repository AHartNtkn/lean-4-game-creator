import Game.Metadata

World "Finale"
Level 1

Title "A New Summation Formula"

Introduction "
# Sum of Products of Consecutive Integers

Prove this identity by induction:

$$3 \\cdot \\sum_{i=0}^{n} i(i+1) = n(n+1)(n+2)$$

Each term $i(i+1)$ is the product of two consecutive integers.
The sum of these products has a clean closed form.

**Verify**: For $n = 2$: $3(0 \\cdot 1 + 1 \\cdot 2 + 2 \\cdot 3) = 3 \\cdot 8 = 24$
and $2 \\cdot 3 \\cdot 4 = 24$. Checks out.

**The proof plan** follows the standard induction pattern from
the SummationFormulas world:

1. **Base case**: Peel `range 1` with `sum_range_succ`, clear
   `range 0` with `sum_range_zero`, close with `ring`
2. **Inductive step**: Peel with `sum_range_succ`, distribute
   with `mul_add`, substitute the IH, close with `ring`
"

/-- The sum of i*(i+1) for i = 0 to n has a closed form. -/
Statement (n : ℕ) :
    3 * ∑ i ∈ Finset.range (n + 1), i * (i + 1) = n * (n + 1) * (n + 2) := by
  Hint "Induct on `n` using natural number induction."
  Hint (hidden := true) "Type `induction n with` then `| zero` then
  `| succ n ih`."
  induction n with
  | zero =>
    Hint "**Base case**: Peel `range 1` and clear `range 0`."
    Hint (hidden := true) "Try
    `rw [Finset.sum_range_succ, Finset.sum_range_zero]`
    then `ring`."
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    Hint "The goal is now a concrete arithmetic identity. Close
    with `ring`."
    Hint (hidden := true) "Try `ring`."
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel the last term from the sum,
    distribute the 3, and substitute the IH."
    Hint (hidden := true) "Try
    `rw [Finset.sum_range_succ, mul_add, ih]`
    then `ring`."
    rw [Finset.sum_range_succ, mul_add, ih]
    Hint "After peeling and substituting:
    - `sum_range_succ` extracted the last term
    - `mul_add` distributed the 3 across the sum
    - `ih` substituted `3 * (sum) = n*(n+1)*(n+2)`

    The remaining goal is polynomial arithmetic. Close with `ring`."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
$$3 \\sum_{i=0}^{n} i(i+1) = n(n+1)(n+2)$$

**The inductive step in detail**:

$$3\\sum_{i=0}^{n+1} i(i+1) = 3\\sum_{i=0}^{n} i(i+1) + 3(n+1)(n+2)$$
$$= n(n+1)(n+2) + 3(n+1)(n+2)$$
$$= (n+1)(n+2)(n+3)$$

The factoring step — pulling out $(n+1)(n+2)$ — is exactly
what `ring` handles automatically.

**The induction pattern** you used:
1. `sum_range_succ` — peel the last term
2. `mul_add` — distribute the multiplier
3. `ih` — substitute the induction hypothesis
4. `ring` — close the polynomial arithmetic

This is the same pattern from the SummationFormulas world,
applied to a new identity. The technique transfers because
the *structure* of the proof is the same — only the formula
changes.

**Combinatorial interpretation**: Since $n(n+1)(n+2) = 6\\binom{n+2}{3}$,
this identity says $\\sum_{i=0}^{n} i(i+1) = 2\\binom{n+2}{3}$.
Each term $i(i+1) = 2\\binom{i+1}{2}$ counts twice the number of
2-element subsets of $\\{0, \\ldots, i\\}$, connecting this summation
formula back to the binomial coefficients from Phase 5.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
