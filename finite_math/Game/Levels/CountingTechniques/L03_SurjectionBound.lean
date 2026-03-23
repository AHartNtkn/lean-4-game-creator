import Game.Metadata

World "CountingTechniques"
Level 3

Title "Surjection Gives a Cardinality Bound"

Introduction "
# Technique 2b: Surjection-Based Bounds

A **surjection** (onto function) from `alpha` to `beta` means every
element of `beta` is hit by at least one element of `alpha`. Therefore
`beta` can't have more elements than `alpha`:

$$f : \\alpha \\twoheadrightarrow \\beta \\text{ surjective} \\implies
|\\beta| \\leq |\\alpha|$$

The Lean theorem is `Fintype.card_le_of_surjective`:

```
Fintype.card_le_of_surjective :
  (f : alpha -> beta) -> Function.Surjective f ->
  Fintype.card beta <= Fintype.card alpha
```

Notice the direction: surjective `f : alpha -> beta` gives `|beta| <= |alpha|`.
This is the **dual** of the injection bound from Level 2.

**Your task**: Given a surjective function `f : alpha -> beta` and
the cardinality of `alpha`, derive a bound on `beta`.
"

/-- A surjective function gives |beta| <= |alpha|. If |alpha| = 7, then |beta| <= 7. -/
Statement (alpha beta : Type*) [Fintype alpha] [Fintype beta] (f : alpha -> beta)
    (hsurj : Function.Surjective f) (halpha : Fintype.card alpha = 7) :
    Fintype.card beta <= 7 := by
  Hint "First, use `Fintype.card_le_of_surjective` to establish
  `Fintype.card beta <= Fintype.card alpha`."
  Hint (hidden := true) "Try:
  `have h := Fintype.card_le_of_surjective f hsurj`"
  have h := Fintype.card_le_of_surjective f hsurj
  Hint "Now combine `h` and `halpha` with `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The surjection bound in two steps:
1. `have h := Fintype.card_le_of_surjective f hsurj` -- establish the bound
2. `omega` -- combine with the known cardinality

**Injection vs. surjection**:

| Function property | Cardinality consequence |
|---|---|
| Injective `f : alpha -> beta` | `|alpha| <= |beta|` |
| Surjective `f : alpha -> beta` | `|beta| <= |alpha|` |

An injection maps `alpha` *into* `beta` (source <= target).
A surjection maps `alpha` *onto* `beta` (target <= source).

**Next**: What if `f` is BOTH injective and surjective? Then you
get both `|alpha| <= |beta|` and `|beta| <= |alpha|`, which together give
`|alpha| = |beta|`. That's the subject of the next level.
"

/-- `Fintype.card_le_of_surjective f hsurj` states that if
`f : alpha -> beta` is surjective, then `Fintype.card beta <= Fintype.card alpha`.

## Syntax
```
have h := Fintype.card_le_of_surjective f hsurj
```
or
```
exact Fintype.card_le_of_surjective f hsurj
```

## When to use it
When you have a surjective function and need a cardinality
lower bound. Surjectivity means every target element is hit,
so the source must be at least as large.
-/
TheoremDoc Fintype.card_le_of_surjective as "Fintype.card_le_of_surjective" in "Fintype"

NewTheorem Fintype.card_le_of_surjective

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
