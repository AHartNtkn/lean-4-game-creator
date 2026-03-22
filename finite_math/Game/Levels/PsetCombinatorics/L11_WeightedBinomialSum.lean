import Game.Metadata

World "PsetCombinatorics"
Level 11

Title "Weighted Binomial Sum"

Introduction "
# Absorption Inside a Sum

You've used the absorption identity to prove equalities between
single expressions. Now use it **inside a sum** to derive:

$$\\sum_{i=0}^{n} i \\cdot \\binom{n}{i} = n \\cdot 2^{n-1}$$

This identity says: if each element of an $n$-element set
contributes its 'weight' (its index in the sum) times the number
of subsets containing it, the total weight is $n \\cdot 2^{n-1}$.

**Why `cases` instead of `induction`?** The hockey stick (Level 7)
used `induction n` because the inductive step *depends on* the
previous case via the induction hypothesis. Here the two branches
($n = 0$ and $n = m + 1$) have completely independent structures —
the successor case does **not** use the zero case. When you don't
need an induction hypothesis, `cases` is the right tool: it splits
without creating an `ih` you'd never use.

**Strategy**:
1. Handle the $n = 0$ case (both sides are $0$)
2. For $n = m + 1$: split off the $i = 0$ term (which is $0$)
3. Apply absorption to transform each remaining summand:
   $(i+1) \\cdot \\binom{m+1}{i+1} = (m+1) \\cdot \\binom{m}{i}$
4. Factor out $(m + 1)$ and apply the row sum
"

/-- The weighted binomial sum: ∑ i * C(n,i) = n * 2^(n-1). -/
Statement (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), i * Nat.choose n i = n * 2 ^ (n - 1) := by
  Hint "Handle the $n = 0$ case separately. Use `cases n`."
  Hint (hidden := true) "Try `cases n` — this creates two goals, one for `zero` and one for `succ m`."
  cases n with
  | zero =>
    Hint "Both sides are $0$ when $n = 0$. Unfold the sum and
    simplify."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zero_mul, zero_mul]`."
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zero_mul, zero_mul]
  | succ m =>
    Hint "The goal shows `2 ^ (m + 1 - 1)` on the right. In natural
    numbers, `(m + 1) - 1 = m`, so this is really `2 ^ m`. Use
    `show` to restate the goal with the simplified exponent.

    The `show` tactic lets you replace the current goal with an
    equivalent statement — here, normalizing the subtraction."
    Hint (hidden := true) "Try `show ∑ i ∈ Finset.range (m + 1 + 1), i * Nat.choose (m + 1) i = (m + 1) * 2 ^ m`."
    show ∑ i ∈ Finset.range (m + 1 + 1), i * Nat.choose (m + 1) i = (m + 1) * 2 ^ m
    Hint "For $n = m + 1$: split off the $i = 0$ term using
    `Finset.sum_range_succ'`, which separates $f(0)$ from the rest
    of the sum."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ']` then simplify the $f(0) = 0$ term."
    rw [Finset.sum_range_succ']
    Hint "The $i = 0$ term is $0 \\cdot C(m+1, 0) = 0$.
    Simplify it away."
    Hint (hidden := true) "Try `rw [zero_mul, add_zero]`."
    rw [zero_mul, add_zero]
    Hint "Now apply absorption to each summand. The absorption
    identity `Nat.add_one_mul_choose_eq m i` says:
    $(m+1) \\cdot C(m, i) = C(m+1, i+1) \\cdot (i+1)$

    Read right-to-left: $(i+1) \\cdot C(m+1, i+1) = (m+1) \\cdot C(m, i)$.

    Prove this pointwise, then apply `Finset.sum_congr rfl`."
    Hint (hidden := true) "Declare:
    `have hab : ∀ i ∈ Finset.range (m + 1), (i + 1) * Nat.choose (m + 1) (i + 1) = (m + 1) * Nat.choose m i := by`

    Then: `intro i _` followed by
    `rw [mul_comm (i + 1)]`
    `exact (Nat.add_one_mul_choose_eq m i).symm`"
    have hab : ∀ i ∈ Finset.range (m + 1),
        (i + 1) * Nat.choose (m + 1) (i + 1) = (m + 1) * Nat.choose m i := by
      intro i _
      rw [mul_comm (i + 1)]
      exact (Nat.add_one_mul_choose_eq m i).symm
    Hint "Apply the pointwise transformation to the whole sum."
    Hint (hidden := true) "Try `rw [Finset.sum_congr rfl hab]`."
    rw [Finset.sum_congr rfl hab]
    Hint "Factor out $(m + 1)$ from the sum using `← Finset.mul_sum`,
    then apply the row sum identity `Nat.sum_range_choose`."
    Hint (hidden := true) "Try `rw [← Finset.mul_sum, Nat.sum_range_choose]`."
    rw [← Finset.mul_sum, Nat.sum_range_choose]

Conclusion "
You derived $\\sum i \\cdot \\binom{n}{i} = n \\cdot 2^{n-1}$ by
using absorption **as a transformation inside a sum** — a
qualitatively different move from applying it to a single
expression.

**Why $n \\cdot 2^{{n-1}}$?** Think of it this way: there are $2^n$
subsets of an $n$-element set. Each of the $n$ elements belongs to
exactly half of those subsets — the $2^{{n-1}}$ subsets that
include it. If you sum 'how many elements does each subset
contain?' across all $2^n$ subsets, each element contributes
$2^{{n-1}}$ (once per subset containing it), and there are $n$
elements, giving $n \\cdot 2^{{n-1}}$ total.

The proof technique: split off the zero term, apply absorption
pointwise via `sum_congr rfl`, factor out the constant with
`← Finset.mul_sum`, and finish with the row sum. This technique
of transforming summands pointwise before evaluating is one the
boss also requires.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
