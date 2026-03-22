import Game.Metadata

World "Finsupp"
Level 9

Title "Accumulation at a Point"

Introduction "
# Same Support Point: Values Add Up

In the last level, you added two singles with *different* support
points (1 and 2) and evaluated at one of them. The other single
contributed `0` at that position.

What happens when both singles share the **same** support point?
The values **accumulate** — they add together at that position.

This is the core property that makes finitely supported functions
behave like formal linear combinations. A polynomial like `-3x⁴ + 5x⁴`
simplifies to `2x⁴` because the coefficients at the same power
add up. The same thing happens with `Finsupp.single`.

**A note on types**: Until now, every level used `ℕ →₀ ℕ`. But
`Finsupp` is general — the domain and codomain can be any types
with the right structure. This level uses `ℕ →₀ ℤ`, where the
values are **integers**. This lets coefficients be negative, which
is essential for polynomials (like `-3x⁴`) and formal linear
combinations in general. All the same lemmas — `add_apply`,
`single_eq_same`, `single_eq_of_ne` — work unchanged.

**Your task**: Evaluate `Finsupp.single 4 (-3) + Finsupp.single 4 5`
at position `4`, where the values are integers.
"

/-- When two singles share a support point, their integer values add. -/
Statement : (Finsupp.single 4 (-3) + Finsupp.single 4 5 : ℕ →₀ ℤ) 4 = 2 := by
  Hint "Start by decomposing the addition with `add_apply`, just
  like in the previous level."
  Hint (hidden := true) "Try `rw [Finsupp.add_apply]`."
  rw [Finsupp.add_apply]
  Hint "Now you have `Finsupp.single 4 (-3) 4 + Finsupp.single 4 5 4 = 2`.
  Both singles are evaluated at their support point `4`. Evaluate
  the first one."
  Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
  rw [Finsupp.single_eq_same]
  Hint "Now evaluate the second single at its support point."
  Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
  rw [Finsupp.single_eq_same]
  Hint (hidden := true) "The goal is now `-3 + 5 = 2`. Try `omega`."
  omega

Conclusion "
Notice the difference from the previous level:

- **Different support points** (Level 8): one single evaluates to its
  value, the other evaluates to `0`. The sum is just the one value.
- **Same support point** (this level): BOTH singles evaluate to their
  values. The sum is the actual sum of the two values: `-3 + 5 = 2`.

This is **accumulation** — the defining behavior of formal linear
combinations. When you write `Finsupp.single 4 (-3) + Finsupp.single 4 5`,
you get a finsupp whose value at `4` is `2`, not `-3` or `5`.

In polynomial language, you just proved that **-3x⁴ + 5x⁴ = 2x⁴**:
`Finsupp.single 4 (-3)` represents the monomial `-3x⁴` (coefficient
`-3` at degree `4`), and evaluating the sum at degree `4` gives
`-3 + 5 = 2`, the combined coefficient. The fact that we used `ℤ`
values made negative coefficients possible — `ℕ` would not allow this.

No new lemmas were needed. The same finsupp evaluation strategy
(`add_apply` → `single_eq_same`) handles both cases, regardless of
whether the value type is `ℕ`, `ℤ`, or any other `AddZeroClass`.
The difference is purely in which evaluation lemma applies to each
summand.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply Finsupp.single_add
