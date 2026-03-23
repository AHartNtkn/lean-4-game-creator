import Game.Metadata

World "CountingTechniques"
Level 2

Title "Injection Gives a Cardinality Bound"

Introduction "
# Technique 2: Injection-Based Bounds

An **injection** (one-to-one function) from type `alpha` to type `beta`
means every element of `alpha` occupies a distinct slot in `beta`.
Therefore `alpha` can't have more elements than `beta`:

$$f : \\alpha \\hookrightarrow \\beta \\text{ injective} \\implies
|\\alpha| \\leq |\\beta|$$

The Lean theorem is `Fintype.card_le_of_injective`:

```
Fintype.card_le_of_injective :
  (f : alpha -> beta) -> Function.Injective f ->
  Fintype.card alpha <= Fintype.card beta
```

**When to reach for this technique**: When you need a cardinality
*inequality* (not equality). An injection gives `<=`.

**Your task**: Given an injective function between finite types
where the target has 10 elements, prove that the source has at
most 10 elements.
"

/-- An injective function gives |alpha| <= |beta|. If |beta| = 10, then |alpha| <= 10. -/
Statement (alpha beta : Type*) [Fintype alpha] [Fintype beta] (f : alpha -> beta)
    (hinj : Function.Injective f) (hbeta : Fintype.card beta = 10) :
    Fintype.card alpha <= 10 := by
  Hint "First, use `Fintype.card_le_of_injective` to establish the
  cardinality bound `Fintype.card alpha <= Fintype.card beta`."
  Hint (hidden := true) "Try:
  `have h := Fintype.card_le_of_injective f hinj`"
  have h := Fintype.card_le_of_injective f hinj
  Hint "Now you have `h : Fintype.card alpha <= Fintype.card beta`
  and `hbeta : Fintype.card beta = 10`. Combine them with `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The injection bound in two steps:
1. `have h := Fintype.card_le_of_injective f hinj` -- establish the bound
2. `omega` -- combine with the known cardinality

**Reading the statement**: `card_le_of_injective` says: if I can
map `alpha` into `beta` without collisions, then `alpha` has at most as
many elements as `beta`. The injection assigns each element of `alpha`
a unique 'slot' in `beta`, so `|alpha| <= |beta|`.

**The surjection dual**: Next level, you'll meet
`Fintype.card_le_of_surjective` -- the surjection version gives
the reverse inequality.

**Coming up**: After learning both bounds, we'll see how combining
them yields equality (the bijection principle).
"

/-- `Fintype.card_le_of_injective f hinj` states that if
`f : alpha -> beta` is injective, then `Fintype.card alpha <= Fintype.card beta`.

## Syntax
```
have h := Fintype.card_le_of_injective f hinj
```
or
```
exact Fintype.card_le_of_injective f hinj
```

## When to use it
When you have an injective function and need a cardinality
upper bound. The injection means distinct inputs go to distinct
outputs, so the source can't be larger than the target.

## Warning
This gives `<=`, not `<`. For strict inequality, you need to
additionally show the function is not surjective — see Level 7.
-/
TheoremDoc Fintype.card_le_of_injective as "Fintype.card_le_of_injective" in "Fintype"

NewTheorem Fintype.card_le_of_injective

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
