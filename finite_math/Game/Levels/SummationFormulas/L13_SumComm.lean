import Game.Metadata

World "SummationFormulas"
Level 13

Title "Swapping Summation Order"

Introduction "
# Double Sums and the Order of Summation

Imagine a grid of numbers — rows indexed by $i$, columns by $j$.
You can add up all the entries by going **row by row** (for each $i$,
sum over all $j$) or **column by column** (for each $j$, sum over
all $i$). Either way, you get the same total.

This is **Fubini's principle for finite sums**: the order of
summation doesn't matter.

$$\\sum_{i \\in \\text{range } n} \\sum_{j \\in \\text{range } m} f(i, j)
= \\sum_{j \\in \\text{range } m} \\sum_{i \\in \\text{range } n} f(i, j)$$

In Lean, this is `Finset.sum_comm`. Note that `f` is completely
arbitrary — the function does NOT need to be symmetric in $i$ and $j$.
The result holds purely because addition is commutative and
associative.

**Why this matters**: In combinatorics, **double counting** is the
technique of computing the same quantity two ways. One direction may
be easy while the other is hard, and equating them gives a non-obvious
identity. `sum_comm` is the formal backbone of double counting — it
lets you switch from the hard direction to the easy one.

**Your task**: Prove the interchange directly using `Finset.sum_comm`
(learned in BigOpAlgebra).
"

/-- The order of a double sum over ranges can be swapped. -/
Statement (n m : ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f i j =
    ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n, f i j := by
  Hint "This is not an induction problem — it's a direct application
  of a structural lemma. The theorem `Finset.sum_comm` states exactly
  this interchange."
  Hint (hidden := true) "Try `exact Finset.sum_comm`."
  exact Finset.sum_comm

Conclusion "
You proved that the order of a double sum can be swapped.

**One line, but not trivial**: The proof is short because `sum_comm`
packages a deep fact — that rearranging a finite sum preserves the
total. The mathematical content is in the *application*, not the
proof.

**When sum_comm solves real problems**: Consider trying to evaluate
$\\sum_{i=0}^{n-1} \\sum_{j=0}^{m-1} g(j)$ where the inner function
doesn't depend on $i$. Summing row-by-row, each row gives the same
value $\\sum_j g(j)$, so the total is $n \\cdot \\sum_j g(j)$.

But what about $\\sum_{i=0}^{n-1} \\sum_{j=0}^{m-1} g(i)$? Now the
inner function doesn't depend on $j$, but it's buried inside the
inner sum. Swapping with `sum_comm` gives
$\\sum_{j=0}^{m-1} \\sum_{i=0}^{n-1} g(i)$, and now the inner sum
doesn't depend on $j$ — same situation as before.

More generally, whenever one summation order leads to a known
formula but the other doesn't, `sum_comm` lets you choose the
productive direction. This is the formal version of 'by symmetry'
or 'interchange the order of summation' that appears throughout
combinatorics and analysis.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.prod_mul_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub Nat.factorial_eq_prod_range_add_one Finset.prod_range_add_one_eq_factorial Finset.sum_range_id_mul_two Finset.sum_range_id
