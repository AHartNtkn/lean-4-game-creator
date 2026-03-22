import Game.Metadata

World "BinomialTheorem"
Level 7

Title "Rewriting Inside a Hypothesis"

Introduction "
# The `have` + `sum_congr` + `rw at h` Pattern

In Level 5, you used `apply Finset.sum_congr rfl` to simplify the
**goal**. But what if the sum you need to simplify is inside a
**hypothesis**?

You cannot `apply` into a hypothesis. Instead, you:

1. Build a proof that each summand simplifies:
   `have simpl : ∀ m ∈ ..., old = new := by intro m _; rw [...]`
2. Use it to rewrite the hypothesis:
   `rw [Finset.sum_congr rfl simpl] at h`

This is the same `sum_congr` from Level 5, but now used with `rw at h`
instead of `apply`.

**Your task**: You are given a hypothesis `h` containing a sum
with `1^m * 1^(n-m) * choose n m`. Simplify the sum inside `h`
to just `choose n m`, then close the goal.

In Level 8, you will create `h` yourself using `add_pow_nat`. Here,
focus on the mechanics of simplifying a sum inside a hypothesis.
"

/-- Simplify a sum inside a hypothesis using the have + sum_congr pattern. -/
Statement (n : ℕ)
    (h : 2 ^ n = ∑ m ∈ Finset.range (n + 1), 1 ^ m * 1 ^ (n - m) * Nat.choose n m) :
    2 ^ n = ∑ m ∈ Finset.range (n + 1), Nat.choose n m := by
  Hint "The sum in `h` has unsimplified terms: `1^m * 1^(n-m) * choose n m`.
  You need to prove each summand simplifies to `choose n m`, then
  rewrite `h`.

  Start by declaring the pointwise simplification:
  `have simpl : ∀ m ∈ Finset.range (n + 1), 1 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m := by`"
  Hint (hidden := true) "Type:
  `have simpl : ∀ m ∈ Finset.range (n + 1), 1 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m := by`

  Then in the sub-proof: `intro m _` followed by
  `rw [one_pow, one_pow, one_mul, one_mul]`."
  have simpl : ∀ m ∈ Finset.range (n + 1),
      1 ^ m * 1 ^ (n - m) * Nat.choose n m = Nat.choose n m := by
    intro m _
    rw [one_pow, one_pow, one_mul, one_mul]
  Hint "Good — you have `simpl` proving the pointwise simplification.
  Now apply it to the sum in `h` using `rw [Finset.sum_congr rfl simpl] at h`.

  Note the `at h` — this rewrites inside the hypothesis, not the goal."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl simpl] at h`."
  rw [Finset.sum_congr rfl simpl] at h
  Hint "Now `h` says `2 ^ n = ∑ m, choose n m` — exactly the goal.
  Close with `exact h`."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
Three steps: declare `simpl`, rewrite `h`, close with `exact h`.

**The `have` + `rw at h` pattern**:

1. `have simpl : ∀ m ∈ ..., f m = g m := by ...` — prove each
   summand simplifies
2. `rw [Finset.sum_congr rfl simpl] at h` — apply to the hypothesis

This is the `apply` form from Level 5, adapted for hypotheses. In
Level 5, you used `apply Finset.sum_congr rfl` on the goal. Here,
you build the proof as a `have` and use `rw` to apply it to `h`.

**Why two forms?** You cannot `apply` into a hypothesis — `apply`
only works on the goal. So when the sum you need to simplify is in
a hypothesis (like after `have h := add_pow_nat ...`), you need the
`have` + `rw at h` form.

In Level 8, you will combine this pattern with `have h := add_pow_nat`
and `exact h.symm` (Level 6) to derive the **row sum identity**.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
DisabledTheorem Nat.sum_range_choose
