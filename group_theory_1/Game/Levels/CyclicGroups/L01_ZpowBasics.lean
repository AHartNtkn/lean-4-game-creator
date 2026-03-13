import Game.Metadata

World "CyclicGroups"
Level 1

Title "Integer Powers"

Introduction
"
In the Commutative Groups world, you met natural-number powers `a ^ n`
where `n : ℕ`. Now we extend to **integer powers** `a ^ k` where
`k : ℤ`. This lets us write `a ^ (-1)` instead of `a⁻¹`, and more
generally `a ^ (-n)` instead of `(a ^ n)⁻¹`.

The three basic lemmas are:

- `zpow_zero`: `a ^ (0 : ℤ) = 1`
- `zpow_one`: `a ^ (1 : ℤ) = a`
- `zpow_neg`: `a ^ (-n) = (a ^ n)⁻¹`

These extend the `pow_zero` and `pow_one` you already know from ℕ-powers.

Use these to prove `a ^ (1 : ℤ) * a ^ (-1 : ℤ) = 1`.
"

/-- `zpow_zero` says: `a ^ (0 : ℤ) = 1`.

The zeroth integer power of any element is the identity, just like
`pow_zero` for natural number powers.

Use `rw [zpow_zero]` to simplify `a ^ (0 : ℤ)` to `1`. -/
TheoremDoc zpow_zero as "zpow_zero" in "Power"

/-- `zpow_one` says: `a ^ (1 : ℤ) = a`.

The first integer power of any element is itself, just like
`pow_one` for natural number powers.

Use `rw [zpow_one]` to simplify `a ^ (1 : ℤ)` to `a`. -/
TheoremDoc zpow_one as "zpow_one" in "Power"

/-- `zpow_neg` says: `a ^ (-n) = (a ^ n)⁻¹`.

A negative integer power is the inverse of the corresponding positive
power. This is the key identity connecting integer powers to inverses.

Use `rw [zpow_neg]` to convert `a ^ (-n)` to `(a ^ n)⁻¹`. -/
TheoremDoc zpow_neg as "zpow_neg" in "Power"

NewTheorem zpow_zero zpow_one zpow_neg

TheoremTab "Power"

DisabledTactic group

Statement (G : Type*) [Group G] (a : G) :
    a ^ (1 : ℤ) * a ^ (-1 : ℤ) = 1 := by
  Hint "Start by simplifying `a ^ (1 : ℤ)` with `rw [zpow_one]`."
  rw [zpow_one]
  Hint "Now convert the negative power: `rw [zpow_neg]` changes
  `a ^ (-1 : ℤ)` to `(a ^ (1 : ℤ))⁻¹`."
  rw [zpow_neg]
  Hint "Simplify the remaining `a ^ (1 : ℤ)` inside the inverse:
  `rw [zpow_one]`."
  rw [zpow_one]
  Hint (hidden := true) "The goal is now `a * a⁻¹ = 1`. Use
  `exact mul_inv_cancel a`."
  exact mul_inv_cancel a

Conclusion
"
Integer powers generalize natural-number powers by allowing negative
exponents. The three key identities are:

- `zpow_zero`: `a ^ (0 : ℤ) = 1`
- `zpow_one`: `a ^ (1 : ℤ) = a`
- `zpow_neg`: `a ^ (-n) = (a ^ n)⁻¹`

In notation: `a ^ (-1 : ℤ)` is just another way of writing `a⁻¹`,
and `a ^ (-n : ℤ)` is `(a ^ n)⁻¹`.

Next: you'll see how integer powers give rise to the subgroup
*generated* by a single element.
"
