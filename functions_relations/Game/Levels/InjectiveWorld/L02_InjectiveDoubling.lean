import Game.Metadata

World "InjectiveWorld"
Level 2

Title "Doubling is Injective"

TheoremTab "Function"

Introduction "
# Same Shape, Different Algebra

Now prove that the doubling function `n ↦ 2 * n` is injective.

The proof shape is identical to Level 1:
1. `intro a b hab` — get `a`, `b`, and `hab : 2 * a = 2 * b`
2. Extract the arithmetic equation
3. `omega` to finish

The only difference is the function — the proof *shape* is the same.
"

/-- The doubling function n ↦ 2 * n is injective on ℕ. -/
Statement : Function.Injective (fun n : ℕ => 2 * n) := by
  Hint "Same shape as Level 1: `intro a b hab`."
  intro a b hab
  Hint "Now extract the equation. The hypothesis `hab` is definitionally
  `2 * a = 2 * b`. Use `have h : 2 * a = 2 * b := hab`."
  Hint (hidden := true) "`have h : 2 * a = 2 * b := hab` then `omega`."
  Branch
    have h : 2 * a = 2 * b := hab
    omega
  change 2 * a = 2 * b at hab
  omega

Conclusion "
Same shape, same result: `intro`, extract the equation, `omega`.

The doubling function is injective because `2 * a = 2 * b` implies
`a = b` — multiplication by a positive constant preserves distinctness.

**Pause and notice**: Levels 1 and 2 had the same proof skeleton:
```
intro a b hab
have h : ... := hab
omega
```

The function changed, but the proof shape did not. This is the
**canonical injectivity proof** for arithmetic functions on ℕ.
Next, you will see a function that is NOT injective — and learn
a completely different proof shape.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith injection
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Nat.succ_injective Nat.succ.inj Nat.mul_left_cancel Nat.mul_right_cancel Nat.add_right_cancel Nat.add_left_cancel
