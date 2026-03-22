import Game.Metadata

World "FinsetImage"
Level 16

Title "Proving Injectivity"

Introduction "
# Proving That a Function Is Injective

To prove `Function.Injective f`, you need to show:

$$\\forall a\\; b,\\; f(a) = f(b) \\implies a = b$$

When `f` is given as an anonymous function `fun n => ...`, Lean's
goal state may display the equation in un-reduced form. The `show`
tactic lets you restate the goal with the function applied:

```
show ∀ a b : ℕ, 3 * a + 7 = 3 * b + 7 → a = b
```

After `show`, use `intro a b h` to introduce the variables and
hypothesis, then derive `a = b` — typically with `omega`.

**Your task**: Prove that `fun n : ℕ => 3 * n + 7` is injective.

If $3a + 7 = 3b + 7$, then $3a = 3b$, so $a = b$.
"

/-- The function n ↦ 3 * n + 7 is injective. -/
Statement : Function.Injective (fun n : ℕ => 3 * n + 7) := by
  Hint "Use `show ∀ a b : ℕ, 3 * a + 7 = 3 * b + 7 → a = b`
  to restate the goal with the function applied."
  Hint (hidden := true) "Alternatively, you can skip `show` and go
  directly with `intro a b h` then `omega` — Lean can handle the
  un-reduced hypothesis."
  show ∀ a b : ℕ, 3 * a + 7 = 3 * b + 7 → a = b
  Hint "Now use `intro a b h` to introduce the variables and
  the hypothesis `h : 3 * a + 7 = 3 * b + 7`."
  intro a b h
  Hint "The goal is `a = b` and you have `h : 3 * a + 7 = 3 * b + 7`.
  This is linear arithmetic — `omega` handles it."
  omega

Conclusion "
The injectivity proof pattern:
1. `show ∀ a b, f a = f b → a = b` — restate with function applied
2. `intro a b h` — introduce variables and hypothesis
3. `omega` (or other arithmetic tactic) — derive `a = b`

The `show` step is needed because `Function.Injective (fun n => ...)`
leaves the function un-applied in the goal. After `show`, the
function is applied and you can work with concrete arithmetic.

**A note on `Finset.map`**: When injectivity is known, Mathlib
provides `Finset.map`, which takes an **embedding** `e : α ↪ β`
(a function bundled with its injectivity proof) rather than a
plain function. The key fact: `Finset.map_eq_image` says
`s.map e = s.image e`. You'll encounter `map` in Mathlib when
working with embeddings like `Fin.castSucc`.

Next: you'll see a concrete counterexample showing WHY
injectivity is needed for intersection, then prove the repair.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
