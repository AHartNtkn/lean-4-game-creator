import Game.Metadata

World "GroupBasics"
Level 2

Title "Deriving Left Identity"

Introduction
"
Now that you've derived `inv_mul_cancel`, you can use it to derive
the other \"redundant\" tool: `one_mul` ($1 * a = a$).

This derivation is much shorter — just four steps. The idea: replace
the `1` with an inverse pair, then re-bracket and cancel.
"

DisabledTheorem one_mul
DisabledTactic group

TheoremTab "Group"

Statement (G : Type*) [Group G] (a : G) : 1 * a = a := by
  Hint "Replace the `1` with `a * a⁻¹` (which equals `1` by
  `mul_inv_cancel`), then re-bracket and cancel.

  Start with `calc 1 * a` and the first step
  `_ = (a * a⁻¹) * a := by rw [← mul_inv_cancel a]`."
  Hint (hidden := true) "Here is the full calc block:
  ```
  calc 1 * a
      _ = (a * a⁻¹) * a   := by rw [← mul_inv_cancel a]
      _ = a * (a⁻¹ * a)   := by rw [mul_assoc]
      _ = a * 1            := by rw [inv_mul_cancel]
      _ = a                := by rw [mul_one]
  ```"
  Branch
    rw [← mul_inv_cancel a, mul_assoc, inv_mul_cancel, mul_one]
  calc 1 * a
      _ = (a * a⁻¹) * a   := by rw [← mul_inv_cancel a]
      _ = a * (a⁻¹ * a)   := by rw [mul_assoc]
      _ = a * 1            := by rw [inv_mul_cancel]
      _ = a                := by rw [mul_one]

Conclusion
"
Both `one_mul` and `inv_mul_cancel` are now derived. The three axioms
`{mul_assoc, mul_one, mul_inv_cancel}` generate everything.

Notice the shared technique: both derivations used the **catalyst
trick** — inserting a self-cancelling pair (`a * a⁻¹` or `a⁻¹ * a`)
to create a stepping stone. This is one of the most common moves in
group theory. You'll see it again when we study conjugation, cosets,
and homomorphisms.

From here on, we'll use all five tools freely — the derivation was
about understanding, not about restricting your toolkit.
"
