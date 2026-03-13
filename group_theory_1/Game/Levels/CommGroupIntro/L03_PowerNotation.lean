import Game.Metadata

World "CommGroupIntro"
Level 3

Title "Powers"

Introduction
"
In any group, you can multiply an element by itself repeatedly.
The notation `a ^ n` means \"multiply `a` by itself `n` times\":

- `a ^ 0 = 1` (the empty product is the identity)
- `a ^ (n + 1) = a ^ n * a` (one more multiplication on the right)

The extra copy of `a` goes on the **right**. There is also a variant
`pow_succ'` that puts it on the left: `a ^ (n + 1) = a * a ^ n`.
Both are equivalent (by associativity), but `pow_succ` is the one
we'll use — it matches how induction naturally unfolds.

So `a ^ 1 = a`, `a ^ 2 = a * a`, `a ^ 3 = a * a * a`, and so on.

In Lean, these definitions are captured by two theorems:

- `pow_zero : a ^ 0 = 1`
- `pow_succ : a ^ (n + 1) = a ^ n * a`

A useful shortcut is `pow_one : a ^ 1 = a`, which follows
immediately from `pow_succ` and `pow_zero`.

Prove that `a ^ 2 = a * a` by unfolding the definition of `^`.

Note: powers work in any `Group` (or even `Monoid`), not just
commutative ones. We're back to `[Group G]` for this level.
"

/-- `pow_zero` says `a ^ 0 = 1` — the zeroth power of any element
is the identity.

This is part of the recursive definition of `^`. -/
TheoremDoc pow_zero as "pow_zero" in "Power"

/-- `pow_succ` says `a ^ (n + 1) = a ^ n * a` — taking one more
power means multiplying by `a` on the right.

This is part of the recursive definition of `^`.

There is also `pow_succ'` which puts the extra `a` on the left:
`a ^ (n + 1) = a * a ^ n`. Both are equivalent. -/
TheoremDoc pow_succ as "pow_succ" in "Power"

/-- `pow_one` says `a ^ 1 = a` — the first power is the element
itself.

This follows from `pow_succ` and `pow_zero`:
`a ^ 1 = a ^ 0 * a = 1 * a = a`. -/
TheoremDoc pow_one as "pow_one" in "Power"

NewTheorem pow_zero pow_succ pow_one

TheoremTab "Power"

Statement (G : Type*) [Group G] (a : G) : a ^ 2 = a * a := by
  Hint "The goal is `a ^ 2 = a * a`. Lean sees `2` as `1 + 1`, so
  `pow_succ` fires automatically: use it to unfold `a ^ 2` to
  `a ^ 1 * a`. Then use `pow_one` to simplify `a ^ 1` to `a`."
  Hint (hidden := true) "`rw [pow_succ, pow_one]` does it in two
  steps. Or expand fully: `rw [pow_succ, pow_succ, pow_zero, one_mul]`."
  Branch
    -- Full expansion without pow_one
    rw [pow_succ, pow_succ, pow_zero, one_mul]
  rw [pow_succ, pow_one]

Conclusion
"
You've met the `^` notation. The recursive definition unfolds neatly:

- `a ^ 0 = 1` (by `pow_zero`)
- `a ^ 1 = a ^ 0 * a = 1 * a = a` (by `pow_succ` + `pow_zero` + `one_mul`)
- `a ^ 2 = a ^ 1 * a = a * a` (by `pow_succ` + `pow_one`)

The shortcut `pow_one` saves a step whenever you see `a ^ 1`.

In the next level, you'll prove that `1 ^ n = 1` for any `n` using
induction — a technique you know from the Natural Number Game.
"
