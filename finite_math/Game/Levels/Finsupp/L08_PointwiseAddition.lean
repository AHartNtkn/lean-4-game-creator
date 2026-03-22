import Game.Metadata

World "Finsupp"
Level 8

Title "Pointwise Addition"

Introduction "
# Adding Finitely Supported Functions

Two finitely supported functions `f g : α →₀ M` can be added.
The result `f + g` is the function that adds values pointwise:

```
Finsupp.add_apply : (f + g) a = f a + g a
```

This is the defining equation for addition of `Finsupp` values.
After rewriting with `add_apply`, you can evaluate each summand
separately using `single_eq_same` and `single_eq_of_ne`.

**A new pattern**: In Level 2, you used `apply Finsupp.single_eq_of_ne`
because the *entire goal* was `single a b a' = 0`. Here, after
rewriting with `add_apply` and `single_eq_same`, the single evaluation
is buried inside a larger arithmetic expression — you cannot `apply` a
lemma that rewrites a subexpression. Instead, you need `rw`, and
`rw [Finsupp.single_eq_of_ne]` requires the inequality proof upfront.
So you manufacture it with `have h : 1 ≠ 2 := by omega` and then
`rw [Finsupp.single_eq_of_ne h]`.

**Your task**: Evaluate `Finsupp.single 1 3 + Finsupp.single 2 5`
at position `1`.
"

/-- Evaluate a sum of two singles at a point. -/
Statement : (Finsupp.single 1 3 + Finsupp.single 2 5 : ℕ →₀ ℕ) 1 = 3 := by
  Hint "Start by decomposing the addition. Use `rw [Finsupp.add_apply]`
  to split `(f + g) 1` into `f 1 + g 1`."
  Hint (hidden := true) "Try `rw [Finsupp.add_apply]`. The goal
  becomes `Finsupp.single 1 3 1 + Finsupp.single 2 5 1 = 3`."
  rw [Finsupp.add_apply]
  Hint "Now evaluate the first single at its support point."
  Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`. The
  first single evaluates to `3`."
  rw [Finsupp.single_eq_same]
  Hint "The second single is evaluated at `1`, but its support point
  is `2`. You need to show these differ and then evaluate."
  Hint (hidden := true) "Establish the inequality with
  `have h : 1 ≠ 2 := by omega`, then
  `rw [Finsupp.single_eq_of_ne h]`."
  have h : 1 ≠ 2 := by omega
  rw [Finsupp.single_eq_of_ne h]
  Hint (hidden := true) "The goal is now `3 + 0 = 3`. Try `omega`."
  omega

Conclusion "
Adding `Finsupp` values is pointwise: `(f + g) a = f a + g a`.
After decomposing with `add_apply`, you evaluate each piece using
the lemmas from earlier levels:

1. `rw [Finsupp.add_apply]` — decompose the sum
2. `rw [Finsupp.single_eq_same]` — evaluate at the support point
3. `have h : a' ≠ a := by omega` then
   `rw [Finsupp.single_eq_of_ne h]` — evaluate away from it

The `have` step is needed because `single_eq_of_ne` requires a
proof that the points differ. You create that proof, name it `h`,
then feed it to the lemma. This `have` pattern — manufacture a
proof of a side condition, name it, then feed it to a lemma — is
a general Lean technique that works whenever a lemma needs a
hypothesis you don't already have in context.

This three-step sequence — `add_apply` → `single_eq_same`/`single_eq_of_ne`
→ arithmetic — is the **finsupp evaluation strategy**. You will use it
whenever you need to compute a concrete value of a sum of singles.

In this level the two singles had *different* support points. In the
next level you will see what happens when they share the same one.
"

/-- `Finsupp.add_apply` decomposes pointwise addition:

`Finsupp.add_apply : (f + g) a = f a + g a`

## Syntax
```
rw [Finsupp.add_apply]
```

## When to use it
When the goal contains `(f + g) a` for finitely supported functions
`f` and `g`. Rewriting splits the evaluation into separate evaluations
of `f` and `g`.

## Example
`rw [Finsupp.add_apply]` on
`(Finsupp.single 1 3 + Finsupp.single 2 5) 1 = 3`
gives `Finsupp.single 1 3 1 + Finsupp.single 2 5 1 = 3`.
-/
TheoremDoc Finsupp.add_apply as "Finsupp.add_apply" in "Finsupp"

TheoremTab "Finsupp"
NewTheorem Finsupp.add_apply

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
