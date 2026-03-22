import Game.Metadata

World "FinsetInduction"
Level 6

Title "Mixing Sums and Cardinality"

Introduction "
# When the Identity Involves card

Some sum identities relate the sum to the cardinality $|s|$. In the
inductive step, you need to peel *both* the sum and the cardinality:

- `Finset.sum_insert ha` peels the sum
- `Finset.card_insert_of_notMem ha` peels the cardinality

You used `card_insert_of_notMem` in L04. Now you'll combine it with
a more complex summand.

**Your task**: Prove that
$\\sum_{x \\in s} (f(x) + 1) = \\Bigl(\\sum_{x \\in s} f(x)\\Bigr) + |s|$

In the inductive step, you'll need to peel three things:
1. The left sum (`sum_insert ha`)
2. The right sum (`sum_insert ha`)
3. The cardinality (`card_insert_of_notMem ha`)

Then apply the IH and close with `ring`.
"

/-- A sum mixing f(x) and a constant relates to the sum of f plus card. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, (f x + 1) = (∑ x ∈ s, f x) + s.card := by
  Hint "Start with finset induction on `s`."
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: Rewrite the sums and cardinality for the empty set.
    You need `sum_empty` (twice) and `card_empty`, then close the arithmetic."
    Hint (hidden := true) "Try
    `rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]`
    then `ring`."
    rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]
    Hint "The goal is `0 = 0 + 0`. Close with `ring`."
    ring
  | @insert a s ha ih =>
    Hint "**Inductive step**: Peel the left sum, the right sum,
    and the cardinality. Then apply the IH and close with `ring`.

    You need three rewrites with `ha`:
    1. `Finset.sum_insert ha` (for the left sum)
    2. `Finset.sum_insert ha` (for the right sum)
    3. `Finset.card_insert_of_notMem ha`"
    Hint (hidden := true) "Try:
    `rw [Finset.sum_insert ha, Finset.sum_insert ha,`
    `    Finset.card_insert_of_notMem ha, ih]`
    then `ring`."
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha, ih]
    Hint "The goal is now pure arithmetic. Close with `ring`."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
When a sum identity involves both `∑ f` and `|s|`, the inductive
step must peel three things:
1. Each sum over `insert a s` (via `sum_insert ha`)
2. The cardinality of `insert a s` (via `card_insert_of_notMem ha`)

The result:
$$\\sum_{x \\in s} (f(x) + 1) = \\sum_{x \\in s} f(x) + |s|$$

This says: adding 1 to each summand adds $|s|$ to the total. In
classical notation, $\\sum(f + 1) = \\sum f + n$ where $n = |s|$.

Notice the pattern in the inductive step: you **collect** known
facts by rewriting (sum_insert, card_insert, IH), then **close**
with an arithmetic tactic (ring or omega). This
**collect-and-close** strategy is universal for induction proofs
in this course — the mathematical thinking goes into choosing
which lemmas to apply; the final arithmetic is mechanical.

The identity `sum_add_distrib` from BigOpAlgebra could also prove
this *without* induction (splitting the sum and using
`card_eq_sum_ones`). But knowing the inductive proof gives you the
tool for identities where no algebraic shortcut exists.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub
