import Game.Metadata

World "Finsupp"
Level 13

Title "Proving Finsupp Equality"

Introduction "
# Extensionality for Finitely Supported Functions

You have used lemmas like `single_add` that state two finitely supported
functions are equal. But how would you *prove* such an equality yourself,
from scratch?

The technique is **extensionality**: two finitely supported functions are
equal if and only if they agree at every point. The tactic `ext a`
converts a goal `f = g` into `∀ a, f a = g a` — or in tactic mode,
it introduces a generic point `a` and asks you to show `f a = g a`.

You used `ext` on `Fin` types back in MeetFin. Here it works the same
way, but on function types: to show two `Finsupp` values are equal,
check that they give the same output at every input.

After applying `ext`, you typically need to reason about an arbitrary
point `a`. For singles, the value depends on whether `a` equals the
support point or not. Use `by_cases h : a = 3` to split into:
- `h : a = 3` — substitute with `rw [h]`, then evaluate with
  `single_eq_same`
- `h : a ≠ 3` — evaluate with `single_eq_of_ne h`

**Your task**: Prove that `single 3 2 + single 3 5 = single 3 7`
using extensionality, without citing `single_add`.
"

/-- Prove function equality from pointwise agreement. -/
Statement : (Finsupp.single 3 2 + Finsupp.single 3 5 : ℕ →₀ ℕ) = Finsupp.single 3 7 := by
  Hint "Use `ext a` to reduce function equality to pointwise equality
  at a generic point `a`."
  Hint (hidden := true) "Try `ext a`. This introduces `a : ℕ` and gives
  you the goal about values at `a`."
  ext a
  Hint "Decompose the left side using `add_apply`."
  Hint (hidden := true) "Try `rw [Finsupp.add_apply]`."
  rw [Finsupp.add_apply]
  Hint "Now you need to evaluate three `single` expressions at point `a`.
  But `a` is a variable — you do not know if `a = 3` or not. Split
  into cases with `by_cases h : a = 3`."
  Hint (hidden := true) "Try `by_cases h : a = 3`. This creates two
  goals: one where `h : a = 3` and one where `h : a ≠ 3`."
  by_cases h : a = 3
  · Hint "In this branch, `a = 3`. Substitute with `rw [h]` to replace
    `a` with `3`, then evaluate all three singles at their support
    point using `single_eq_same`."
    Hint (hidden := true) "Try `rw [h]` then
    `rw [Finsupp.single_eq_same, Finsupp.single_eq_same, Finsupp.single_eq_same]`."
    rw [h]
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same, Finsupp.single_eq_same]
  · Hint "In this branch, `a ≠ 3`. All three singles have support point
    `3`, so evaluating at `a` gives `0` for each."
    Hint (hidden := true) "Try
    `rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h]`
    then `omega` to close `0 + 0 = 0`."
    rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h]
    Hint (hidden := true) "The goal is `0 + 0 = 0`. Try `omega`."
    omega

Conclusion "
You proved function equality from scratch using extensionality!

The pattern:
1. `ext a` — reduce `f = g` to `f a = g a` for arbitrary `a`
2. `by_cases h : a = n` — split on whether `a` is the support point
3. In each branch, evaluate using `single_eq_same` or `single_eq_of_ne`

This is exactly how `single_add` is proved internally: apply `ext`,
then check both cases. The lemma packages this up so you do not need
to do the case analysis every time.

Extensionality is the standard technique for proving equality of
function-like objects. You will use it again when working with
matrices — proving two matrices are equal by checking every entry.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply Finsupp.single_add
