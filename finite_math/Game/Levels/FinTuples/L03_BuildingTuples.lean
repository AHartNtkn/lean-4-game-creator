import Game.Metadata

World "FinTuples"
Level 3

Title "Building Tuples"

Introduction "
# Building a Tuple Step by Step

You've seen how to *read* tuples. Now let's *build* one.

The goal asks: does there exist a function `Fin 3 → ℕ` that maps
`0` to `10`, `1` to `20`, and `2` to `30`?

You already know such a function: `![10, 20, 30]`. The strategy:

1. **`use ![10, 20, 30]`** — provide the witness
2. **`constructor`** — split the conjunction `P ∧ Q` into two goals
3. **`rfl`** — each equation holds by definition

This is the same `constructor` + `rfl` pattern you'll use
throughout this world whenever you need to verify properties of
a specific tuple.

**Your task**: Build `![10, 20, 30]` and verify its values.
"

/-- A function `Fin 3 → ℕ` that maps 0 to 10, 1 to 20, and 2 to 30. -/
Statement : ∃ f : Fin 3 → ℕ, f 0 = 10 ∧ f 1 = 20 ∧ f 2 = 30 := by
  Hint "Provide the tuple with `use ![10, 20, 30]`."
  use ![10, 20, 30]
  Hint "The goal is now `![10, 20, 30] 0 = 10 ∧ ...`.
  Use `constructor` to split the conjunction."
  constructor
  · Hint "The goal is `![10, 20, 30] 0 = 10`. Use `rfl`."
    rfl
  · Hint "Use `constructor` to split the remaining conjunction."
    constructor
    · Hint "Use `rfl`."
      rfl
    · Hint "Use `rfl`."
      rfl

Conclusion "
You built a 3-tuple and verified its values step by step:

1. `use` provided the witness `![10, 20, 30]`
2. `constructor` split each `∧` into separate goals
3. `rfl` closed each equation (the values are definitional)

This `use` + `constructor` + `rfl` pattern will return
throughout this world — you'll use it in the next few levels
to verify properties of `Fin.cons` and `vecSnoc`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
