import Game.Metadata

World "PsetBigOp"
Level 8

Title "Boss: Squared Differences"

Introduction "
# Boss: Summing Squared Differences

Prove by finset induction:

$$\\sum_{x \\in s} \\bigl((f(x)+1)^2 - f(x)^2\\bigr) = 2 \\cdot \\sum_{x \\in s} f(x) + |s|$$

The summand $(f(x)+1)^2 - f(x)^2$ involves natural number
subtraction inside a sum — a new surface form. Each individual
term is well-behaved ($(k+1)^2 > k^2$ always), but `ring` can't
handle natural number subtraction directly.

**Strategy**: In the inductive step, after peeling all three
quantities (left sum, right sum, cardinality), use the
`have` + `ring` + `omega` technique from SummationFormulas:

1. Establish $(f(a)+1)^2 = f(a)^2 + 2 \\cdot f(a) + 1$ with `ring`
2. Let `omega` handle the resulting linear arithmetic (it uses
   the `have` to resolve the subtraction, and the IH for the rest)

**Moves integrated**:
- Finset induction setup (FinsetInduction)
- `sum_insert ha` (BigOpIntro)
- `card_insert_of_notMem ha` (FinsetInduction)
- `have ... := by ring` (SummationFormulas)
- `omega` with IH (SummationFormulas)
"

/-- The sum of (f(x)+1)^2 - f(x)^2 over s equals 2 times the sum of f plus card. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, ((f x + 1) ^ 2 - f x ^ 2) = 2 * ∑ x ∈ s, f x + s.card := by
  Hint "This is a finset induction problem. Set up induction on `s`."
  Hint (hidden := true) "Type:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint (hidden := true) "Rewrite both sums and the cardinality:
    `rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]`
    then `ring`."
    rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]
    ring
  | @insert a s ha ih =>
    Hint "**Inductive step**: Peel three things using `ha`:
    1. The left sum with `Finset.sum_insert ha`
    2. The right sum with `Finset.sum_insert ha`
    3. The cardinality with `Finset.card_insert_of_notMem ha`

    Then use `have` to establish the key ring identity, and
    let `omega` close the goal using both `ih` and `have`."
    Hint (hidden := true) "Try:
    `rw [Finset.sum_insert ha, Finset.sum_insert ha,`
    `    Finset.card_insert_of_notMem ha]`
    then:
    `have h : (f a + 1) ^ 2 = f a ^ 2 + 2 * f a + 1 := by ring`
    then `omega`."
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha]
    Hint "After peeling, the goal has `(f a + 1) ^ 2 - f a ^ 2`.
    `ring` can't handle natural subtraction, and `omega` alone
    can't see that `(f a + 1) ^ 2 = f a ^ 2 + 2 * f a + 1`.

    Use `have` to bridge: establish the polynomial identity with
    `ring`, then `omega` resolves the subtraction and applies `ih`."
    Hint (hidden := true) "Try:
    `have h : (f a + 1) ^ 2 = f a ^ 2 + 2 * f a + 1 := by ring`
    then `omega`."
    have h : (f a + 1) ^ 2 = f a ^ 2 + 2 * f a + 1 := by ring
    omega

Conclusion "
Congratulations! You've completed the **Big Operators Problem Set**.

You proved:
$$\\sum_{x \\in s} \\bigl((f(x)+1)^2 - f(x)^2\\bigr) = 2\\sum_{x \\in s} f(x) + |s|$$

**Why this identity is true**: Each term $(f(x)+1)^2 - f(x)^2$ equals
$2f(x) + 1$. Summing over $s$: $\\sum (2f(x) + 1) = 2\\sum f(x) + |s|$.
The identity is a special case of the algebraic fact
$(a+1)^2 - a^2 = 2a + 1$, applied element-wise and summed.

**The `have` + `ring` + `omega` technique**: When a goal involves
natural number subtraction or nonlinear expressions:
- `ring` can prove polynomial identities but can't handle subtraction
- `omega` can handle linear arithmetic with subtraction but not
  nonlinear expressions

The `have` bridges the gap: `ring` proves the polynomial fact,
then `omega` treats the polynomial terms as opaque variables and
solves the resulting linear problem.

**Skills integrated in this boss**:
1. `Finset.induction_on` (FinsetInduction)
2. `sum_insert ha` (BigOpIntro)
3. `card_insert_of_notMem ha` (FinsetInduction)
4. `have ... := by ring` (SummationFormulas)
5. `omega` with IH (SummationFormulas)
6. `sum_empty`, `card_empty`, `ring` (base case)
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.mul_sum Finset.sum_mul Finset.sum_add_distrib Finset.sum_congr
