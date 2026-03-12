import Game.Metadata

World "HomDef"
Level 4

Title "Deriving `map_one`"

Introduction
"
Does a homomorphism send `1` to `1`? Yes — and you can **derive** it
from `map_mul` alone. This is the key insight: the single axiom
`f(a · b) = f(a) · f(b)` forces `f(1) = 1`.

Here's the idea: `f(1) = f(1 · 1) = f(1) · f(1)`. If `f(1) · f(1) = f(1)`,
then cancelling one copy of `f(1)` gives `f(1) = 1`.

Strategy:
1. `apply mul_left_cancel (a := f 1)` — reduce the goal to
   `f 1 * f 1 = f 1 * 1` (an equation you can cancel from)
2. Simplify `f 1 * 1` to `f 1` using `mul_one`
3. Rewrite `f 1 * f 1` as `f (1 * 1)` using `← map_mul`
4. Simplify `1 * 1` to `1` using `mul_one`

`map_one` is disabled for this level — you must derive it.
"

/-- `map_one` says: for any group homomorphism `f : G →* H`,

`f 1 = 1`

A homomorphism sends the identity to the identity. This is a
consequence of `map_mul` (not an extra axiom).

Use `rw [map_one]` to simplify `f 1` to `1`. -/
TheoremDoc map_one as "map_one" in "Hom"

NewTheorem map_one

TheoremTab "Hom"

DisabledTactic group simp
DisabledTheorem map_one

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) :
    f 1 = 1 := by
  Hint "The trick: show that `f 1` satisfies `f 1 * f 1 = f 1 * 1`,
  then cancel. Use `apply mul_left_cancel (a := f 1)` to set this up."
  apply mul_left_cancel (a := f 1)
  Hint "The goal is `f 1 * f 1 = f 1 * 1`. Start by simplifying the
  right side: `rw [mul_one]`."
  rw [mul_one]
  Hint "The goal is `f 1 * f 1 = f 1`. Now rewrite the left side
  using `← map_mul`: the product `f 1 * f 1` becomes `f (1 * 1)`.

  Try `rw [← map_mul]`."
  rw [← map_mul]
  Hint (hidden := true) "The goal is `f (1 * 1) = f 1`. Use
  `rw [mul_one]` to simplify `1 * 1` to `1`."
  rw [mul_one]

Conclusion
"
You just derived `map_one` from `map_mul` alone:

1. From `f(1 · 1) = f(1) · f(1)` (by `map_mul`)
2. And `1 · 1 = 1` (by `mul_one`)
3. We get `f(1) = f(1) · f(1)`
4. Cancelling gives `1 = f(1)`

This is the **hom-property move** in its purest form: use `map_mul` to
transform the expression, then simplify with group algebra.

From now on, use `map_one` directly — you've earned it. The pattern
\"push the hom through, then simplify\" will recur constantly.

*Aside*: preserving identity alone does NOT make a function a
homomorphism. Many functions satisfy `f(1) = 1` without satisfying
`f(a · b) = f(a) · f(b)`. The axiom `map_mul` is strictly stronger.
"
