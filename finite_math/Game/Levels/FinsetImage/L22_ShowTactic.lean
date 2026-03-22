import Game.Metadata

World "FinsetImage"
Level 22

Title "Using show for Injectivity"

Introduction "
# Restating the Goal with show

In FinsetOperations, you learned that `show` lets you restate the
current goal in an equivalent form that Lean can verify. This is
especially useful for injectivity proofs.

When Lean displays `Function.Injective (fun n => n * 2)`, the goal
is abstract — you can't directly `intro` the arguments. But
`Function.Injective f` unfolds to `∀ a b, f a = f b → a = b`. The
`show` tactic lets you restate with the function applied:

```
show ∀ a b : ℕ, a * 2 = b * 2 → a = b
```

After this, `intro a b h` gives concrete variables and `omega`
finishes the arithmetic.

**Your task**: Prove that doubling is injective by restating with
`show` and then using `intro` and `omega`.
"

/-- Prove injectivity by restating with show. -/
Statement : Function.Injective (fun n : ℕ => n * 2) := by
  Hint "The goal is `Function.Injective (fun n => n * 2)`.
  This unfolds to `∀ a b, a * 2 = b * 2 → a = b`.
  Use `show ∀ a b : ℕ, a * 2 = b * 2 → a = b` to make
  this explicit with the function applied."
  show ∀ a b : ℕ, a * 2 = b * 2 → a = b
  Hint "Now `intro a b h` gives you concrete variables and an
  equation `h : a * 2 = b * 2`. Then `omega` solves it."
  Hint (hidden := true) "Try `intro a b h; omega`."
  intro a b h
  omega

Conclusion "
The `show` tactic is useful when:
- The goal involves an abstract definition (like `Function.Injective`)
- You want to see the definition expanded with specific arguments
- The expanded form is easier to work with

For injectivity proofs, the pattern is always:
1. `show ∀ a b : α, f a = f b → a = b` — expand the definition
2. `intro a b h` — introduce the variables and the equality
3. Prove `a = b` from `h` (often `omega` or algebraic reasoning)

The boss will use this pattern as part of a larger proof.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
