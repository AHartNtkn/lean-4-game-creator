import Game.Metadata

World "GroupBasics"
Level 7

Title "Inverse Uniqueness"

Introduction
"
If `a * b = 1`, what can you conclude about `b`? It must be `a⁻¹` —
the inverse is **unique**.

This theorem is the key to proving that specific expressions equal
specific inverses. Instead of manipulating `(a * b)⁻¹` directly
(which is hard), you can show that something *behaves like* the
inverse and conclude it *is* the inverse.

The proof is a short `calc` chain using `inv_mul_cancel_left`.
"

/-- `inv_eq_of_mul_eq_one_right` says that if `a * b = 1`, then `a⁻¹ = b`.

The inverse is unique: if `b` is a right inverse of `a`, then `b`
must equal `a⁻¹`. This is the main tool for proving that a specific
expression equals an inverse. -/
TheoremDoc inv_eq_of_mul_eq_one_right as "inv_eq_of_mul_eq_one_right" in "Cancel"

NewTheorem inv_eq_of_mul_eq_one_right

DisabledTactic group

TheoremTab "Cancel"

Statement (G : Type*) [Group G] (a b : G) (h : a * b = 1) :
    a⁻¹ = b := by
  Hint "You need to show `a⁻¹ = b`. The idea: start from `a⁻¹`,
  introduce `a * b` (which equals `1` by `h`), then cancel.

  Try a `calc` block:
  ```
  calc a⁻¹ = a⁻¹ * 1 := by ...
       _ = ...
  ```"
  Hint (hidden := true) "The full proof:
  ```
  calc a⁻¹ = a⁻¹ * 1       := by rw [mul_one]
       _ = a⁻¹ * (a * b)    := by rw [← h]
       _ = b                 := by rw [inv_mul_cancel_left]
  ```"
  Branch
    -- calc proof
    calc a⁻¹ = a⁻¹ * 1       := by rw [mul_one]
         _ = a⁻¹ * (a * b)    := by rw [← h]
         _ = b                 := by rw [inv_mul_cancel_left]
  Branch
    -- Direct exact
    exact inv_eq_of_mul_eq_one_right h
  -- rw chain proof
  rw [← mul_one a⁻¹, ← h, inv_mul_cancel_left]

Conclusion
"
You've learned a powerful general technique: **to show `x⁻¹ = y`,
prove `x * y = 1` and apply inverse uniqueness.** This avoids
manipulating `x⁻¹` directly — which is usually hard — and instead
lets you work with ordinary multiplication.

This theorem says something deeper: to verify that `b` is the inverse
of `a`, you only need to check **one** equation (`a * b = 1`). You
don't need to separately check `b * a = 1` — right inverses are
automatically two-sided. This is a special property of groups.

This technique will power the rest of this world. Both the double-
inverse identity and the boss level use exactly this pattern:
`apply inv_eq_of_mul_eq_one_right`, then close the multiplication
goal with cancellation lemmas.
"
