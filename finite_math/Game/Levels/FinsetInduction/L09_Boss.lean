import Game.Metadata

World "FinsetInduction"
Level 9

Title "Boss: Combining Sums and Cardinality"

Introduction "
# Boss: A Sum Identity with Cardinality

Prove the following identity by finset induction:

$$\\sum_{x \\in s} (2 \\cdot f(x) + 3) = 2 \\cdot \\sum_{x \\in s} f(x) + 3 \\cdot |s|$$

This says: if you double each value and add $3$, the total is twice
the original sum plus $3$ times the number of elements.

**What you need** (all from this world):
- `Finset.induction_on` — set up the induction
- `Finset.sum_insert ha` — peel each sum over `insert a s`
- `Finset.card_insert_of_notMem ha` — peel the cardinality
- The induction hypothesis `ih`
- `ring` — close the algebra
"

/-- The sum of (2f + 3) equals twice the sum of f plus 3 times card. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, (2 * f x + 3) = 2 * (∑ x ∈ s, f x) + 3 * s.card := by
  Hint "This is a finset induction problem. Set up induction on `s`
  using `Finset.induction_on`."
  Hint (hidden := true) "Type:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: Simplify both sums over `∅` and `card ∅`.
    You need three rewrites: `sum_empty` (twice) and `card_empty`.
    Then close the arithmetic."
    Hint (hidden := true) "Try
    `rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]`
    then `ring`."
    rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]
    ring
  | @insert a s ha ih =>
    Hint "**Inductive step**: Peel three things using `ha`:
    1. The left sum — `Finset.sum_insert ha`
    2. The right sum — `Finset.sum_insert ha`
    3. The cardinality — `Finset.card_insert_of_notMem ha`

    Then apply `ih` and close with `ring`."
    Hint (hidden := true) "Try:
    `rw [Finset.sum_insert ha, Finset.sum_insert ha,`
    `    Finset.card_insert_of_notMem ha, ih]`
    then `ring`."
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha, ih]
    Hint "The goal is now pure algebra. `ring` closes it."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
Congratulations! You proved a non-trivial sum identity entirely by
finset induction.

**The identity**:
$$\\sum_{x \\in s} (2f(x) + 3) = 2\\sum_{x \\in s} f(x) + 3|s|$$

**Your proof used every tool from this world**:
1. `Finset.induction_on` — the induction principle
2. `sum_insert ha` — peeling sums over `insert a s`
3. `card_insert_of_notMem ha` — peeling cardinality
4. The induction hypothesis — linking `s` to `insert a s`
5. `ring` — closing the algebra

This is the **collect-and-close** strategy in its complete form:
collect all the pieces by rewriting (peel lemmas + IH), then close
the resulting arithmetic mechanically. The mathematical thinking is
in recognizing which quantities need peeling and choosing the right
lemmas — the algebra is left to `ring`.

**Looking ahead**: The SummationFormulas world applies a variant of
this pattern — natural number induction combined with
`sum_range_succ` — to prove classical formulas like the Gauss sum,
geometric sums, and the sum of odd numbers.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub
