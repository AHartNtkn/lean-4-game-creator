import Game.Metadata

World "Finsupp"
Level 16

Title "Support Workout"

Introduction "
# Putting Support and Evaluation Together

Before the boss, let's practice combining several skills. You will
prove four facts:

1. **The support of a nonzero single** is the singleton — using
   `support_single_ne_zero` from Level 3.

2. **A zero-valued single has empty support** — using `single_zero`
   from Level 4.

3. **Support membership via evaluation** — converting a support
   question to a value computation and then evaluating, combining
   `mem_support_iff`, `add_apply`, `single_eq_same`, and
   `single_eq_of_ne`.

4. **Support of a sum is bounded** — using `support_add` to show
   that an element in the support of a sum is in the union of
   the individual supports.

This is the longest proof you have encountered in this world.
Take it one conjunction at a time — use `constructor` to split
each `∧`, then handle one part before moving to the next.
"

/-- Practice support reasoning with evaluation and support_add. -/
Statement :
    (Finsupp.single 2 4 : ℕ →₀ ℕ).support = {2}
    ∧ (Finsupp.single 7 0 : ℕ →₀ ℕ).support = ∅
    ∧ 3 ∈ (Finsupp.single 3 6 + Finsupp.single 9 1 : ℕ →₀ ℕ).support
    ∧ ∀ x ∈ (Finsupp.single 1 2 + Finsupp.single 4 3 : ℕ →₀ ℕ).support,
        x ∈ (Finsupp.single 1 2 : ℕ →₀ ℕ).support ∪ (Finsupp.single 4 3 : ℕ →₀ ℕ).support := by
  Hint "Split the first conjunction with `constructor`."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Part 1: support of a nonzero single
  Hint "**Part 1**: The support of `single 2 4` is the singleton
  containing `2`. Use `support_single_ne_zero`."
  Hint (hidden := true) "Try `apply Finsupp.support_single_ne_zero`.
  This leaves the goal `4 ≠ 0`."
  · apply Finsupp.support_single_ne_zero
    Hint (hidden := true) "Try `omega`."
    omega
  -- Parts 2, 3, and 4
  · Hint "Split the remaining conjunction."
    Hint (hidden := true) "Try `constructor`."
    constructor
    -- Part 2: support of a zero-valued single
    · Hint "**Part 2**: The single `single 7 0` has value zero, so it
      IS the zero function. Rewrite with `single_zero`."
      Hint (hidden := true) "Try `rw [Finsupp.single_zero]`. The
      support of the zero function is empty by definition."
      rw [Finsupp.single_zero]
      Hint (hidden := true) "The goal is now `(0 : ℕ →₀ ℕ).support = ∅`.
      Try `rfl` — this holds by definition."
      rfl
    -- Parts 3 and 4
    · Hint "Split the remaining conjunction."
      Hint (hidden := true) "Try `constructor`."
      constructor
      -- Part 3: support membership via evaluation
      · Hint "**Part 3**: Prove `3 ∈ (single 3 6 + single 9 1).support`.
        Convert support membership to a value statement."
        Hint (hidden := true) "Try `rw [Finsupp.mem_support_iff]`."
        rw [Finsupp.mem_support_iff]
        Hint "Decompose the addition."
        Hint (hidden := true) "Try `rw [Finsupp.add_apply]`."
        rw [Finsupp.add_apply]
        Hint "Evaluate the first single at its support point."
        Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
        rw [Finsupp.single_eq_same]
        Hint "The second single has support point `9`, not `3`.
        Establish the inequality."
        Hint (hidden := true) "Try `have h : 3 ≠ 9 := by omega`
        then `rw [Finsupp.single_eq_of_ne h]`."
        have h : 3 ≠ 9 := by omega
        rw [Finsupp.single_eq_of_ne h]
        Hint "The goal is now a concrete arithmetic inequality."
        Hint (hidden := true) "Try `omega`."
        omega
      -- Part 4: support_add retrieval
      · Hint "**Part 4**: Given `x` in the support of a sum, show it
        is in the union of the individual supports. This is exactly
        what `Finsupp.support_add` gives you."
        Hint (hidden := true) "Try `intro x hx` to introduce the
        element and its membership proof."
        intro x hx
        Hint "Now apply `Finsupp.support_add` to the membership proof."
        Hint (hidden := true) "Try `exact Finsupp.support_add hx`."
        exact Finsupp.support_add hx

Conclusion "
You combined five different skills in a single proof:
- `support_single_ne_zero` to compute the support of a single
- `single_zero` to recognize when a single is the zero function
- `mem_support_iff` to convert between support membership and values
- The full evaluation strategy (`add_apply` → `single_eq_same` /
  `single_eq_of_ne`) to compute a concrete value
- `support_add` to bound the support of a sum by the union

This is the complete Finsupp toolkit. You are ready for the boss.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply Finsupp.single_add
