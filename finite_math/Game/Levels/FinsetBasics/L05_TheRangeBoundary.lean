import Game.Metadata

World "FinsetBasics"
Level 5

Title "The Range Boundary"

Introduction "
# The Range Boundary

`Finset.range 5 = {0, 1, 2, 3, 4}`. Note that `5` itself is **not**
in the range. This is a common source of off-by-one errors.

To prove `5 ∉ Finset.range 5`, you need to prove a **non-membership**
statement. The `∉` symbol means `¬ ∈` — i.e., the membership is false.

The proof pattern for non-membership:
1. `intro h` — assume `h : 5 ∈ Finset.range 5` (proof by contradiction)
2. `rw [Finset.mem_range] at h` — convert to `h : 5 < 5`
3. `omega` — contradiction (`5 < 5` is false)

This is the first time you'll rewrite **a hypothesis** rather than
the goal. The `at h` modifier tells `rw` to rewrite inside `h`.
You practiced this in the Fin worlds — the same `at` modifier works
for any rewrite.
"

/-- 5 is NOT in the range {0, 1, 2, 3, 4}. -/
Statement : (5 : ℕ) ∉ Finset.range 5 := by
  Hint "The goal is `5 ∉ Finset.range 5`, which means
  `¬ (5 ∈ Finset.range 5)`. Use `intro h` to assume
  `h : 5 ∈ Finset.range 5` and aim for a contradiction."
  intro h
  Hint "Now you have `{h}` and the goal is `False`.
  Rewrite `{h}` using `rw [Finset.mem_range] at h` to get
  `h : 5 < 5`."
  rw [Finset.mem_range] at h
  Hint "Now `{h}` is contradictory. `omega` sees this
  and closes the goal."
  omega

Conclusion "
The non-membership pattern:
1. `intro h` — assume membership
2. `rw [... ] at h` — unfold to something concrete
3. `omega` — derive a contradiction

This is **proof by contradiction** in a very targeted form: you don't
need to invoke any fancy contradiction tactic — just show that the
hypothesis leads to a false arithmetic statement.

This pattern extends beyond `range`. In the next level, you'll use
the same technique to prove that `Finset.range 0` is empty — the
ultimate boundary case.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.not_mem_range_self
