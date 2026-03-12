import Game.Metadata

World "CyclicGroups"
Level 5

Title "The Order of an Element"

Introduction
"
Every element of a group has an **order**: the smallest positive
integer `n` such that `g ^ n = 1`. In Lean, this is `orderOf g`.

If no such `n` exists (the element has infinite order), then
`orderOf g = 0` by convention.

Two key lemmas:

- `pow_orderOf_eq_one`: `g ^ orderOf g = 1`
  (the defining property — raising `g` to its order gives `1`)

- `orderOf_one`: `orderOf (1 : G) = 1`
  (the identity has order `1` since `1^1 = 1`)

Given `pow_orderOf_eq_one`, prove that `g ^ (2 * orderOf g) = 1`.
The idea: `g ^ (2 * orderOf g) = (g ^ orderOf g) ^ 2 = 1 ^ 2 = 1`.

You'll need `pow_mul` to rewrite `g ^ (2 * orderOf g)` as
`(g ^ orderOf g) ^ 2`. (Remember: `pow_mul` is for ℕ-powers, saying
`a ^ (m * n) = (a ^ m) ^ n`.)
"

/-- `orderOf g` is the **order** of the group element `g`: the
smallest positive `n : ℕ` such that `g ^ n = 1`.

If `g` has infinite order (no such `n` exists), then `orderOf g = 0`.

Key properties:
- `pow_orderOf_eq_one`: `g ^ orderOf g = 1`
- `orderOf_one`: `orderOf (1 : G) = 1`
- `orderOf_eq_one_iff`: `orderOf g = 1 ↔ g = 1` -/
DefinitionDoc orderOf as "orderOf"

NewDefinition orderOf

/-- `pow_orderOf_eq_one` says: `g ^ orderOf g = 1`.

This is the defining property of `orderOf`: raising an element to its
order gives the identity.

Use `rw [pow_orderOf_eq_one]` or `exact pow_orderOf_eq_one g` to
apply this fact. -/
TheoremDoc pow_orderOf_eq_one as "pow_orderOf_eq_one" in "Cyclic"

/-- `orderOf_one` says: `orderOf (1 : G) = 1`.

The identity element has order `1` since `1 ^ 1 = 1`. -/
TheoremDoc orderOf_one as "orderOf_one" in "Cyclic"

/-- `pow_mul` says: `a ^ (m * n) = (a ^ m) ^ n`.

This splits a product exponent into iterated exponentiation.

Use `rw [pow_mul]` to convert `a ^ (m * n)` into `(a ^ m) ^ n`. -/
TheoremDoc pow_mul as "pow_mul" in "Power"

NewTheorem pow_orderOf_eq_one orderOf_one pow_mul

TheoremTab "Cyclic"

DisabledTactic group

Statement (G : Type*) [Group G] (g : G) :
    g ^ (2 * orderOf g) = 1 := by
  Hint "The exponent `2 * orderOf {g}` can be split using `pow_mul`:
  `a ^ (m * n) = (a ^ m) ^ n`. But `pow_mul` splits as
  `({g} ^ 2) ^ orderOf {g}`, and we need `orderOf {g}` as the base
  exponent for `pow_orderOf_eq_one` to fire.

  Start with `rw [mul_comm]` to rearrange the exponent to
  `orderOf {g} * 2`.

  (Note: `mul_comm` here rearranges the **natural number** exponents
  `2` and `orderOf {g}`, not group elements.)"
  Branch
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  rw [mul_comm]
  Hint "Now `rw [pow_mul]` splits `{g} ^ (orderOf {g} * 2)` into
  `({g} ^ orderOf {g}) ^ 2`."
  rw [pow_mul]
  Hint "Use `rw [pow_orderOf_eq_one]` to simplify `{g} ^ orderOf {g}`
  to `1`."
  rw [pow_orderOf_eq_one]
  Hint (hidden := true) "The goal is `1 ^ 2 = 1`. Use `rw [one_pow]`."
  rw [one_pow]

Conclusion
"
The key insight: `pow_orderOf_eq_one` says `g ^ orderOf g = 1`, and
any multiple of `orderOf g` also gives `1`:

`g ^ (k * orderOf g) = (g ^ orderOf g) ^ k = 1 ^ k = 1`

The `mul_comm` step was needed because `pow_mul` splits `a ^ (m * n)`
as `(a ^ m) ^ n` — the first factor in the product becomes the base.
To get `pow_orderOf_eq_one` to fire, we need `orderOf g` as that
first factor.

On paper: *\"The order of `g` is the period of the sequence
`1, g, g², g³, ...`. After `orderOf g` steps, the sequence returns
to `1` and repeats.\"*

The order of an element is deeply connected to `zpowers g`: the
number of distinct elements in `zpowers g` equals `orderOf g`
(for finite-order elements). This connection drives the theory of
cyclic groups.
"
