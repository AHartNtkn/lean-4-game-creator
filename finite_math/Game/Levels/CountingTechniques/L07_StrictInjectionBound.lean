import Game.Metadata

World "CountingTechniques"
Level 7

Title "Strict Injection Bound"

Introduction "
# Injection + Non-Surjectivity = Strict Inequality

Level 2 proved that an injective function gives `|source| <= |target|`.
But Level 2's documentation noted: 'This gives `<=`, not `<`. For strict
inequality, you need to additionally show the function is not surjective.'

This level delivers on that promise.

**The claim**: If `f : Fin m -> Fin n` is injective but NOT surjective,
then `m < n` (strictly).

**Why?** Injection gives `m <= n`. If `m = n`, then an injective
function between types of equal size is automatically surjective --
there's nowhere for the 'gaps' to go. But we assumed `f` is not
surjective, so `m != n`. Combined with `m <= n`, this gives `m < n`.

**The key theorem**: `Finite.surjective_of_injective` says that
for finite types, an injective function from a type to itself is
automatically surjective. When `m = n`, `Fin m = Fin n`, so `f`
becomes an endofunction.

**New tactic -- `subst`**: If you have `heq : m = n`, then `subst heq`
replaces all occurrences of `n` with `m` throughout the goal and
context. This is how we turn `f : Fin m -> Fin n` into
`f : Fin m -> Fin m` after establishing `m = n`.

**Connection to Level 6**: Level 6 proved strict subset implies
strict cardinality inequality using `card_lt_card`. This level proves
the function-theoretic version: injection without surjectivity implies
strict inequality. Both capture the same idea -- 'fits inside but
doesn't fill.'

**Your task**: Prove `m < n` from injection + non-surjectivity.
"

/-- Injection + non-surjectivity gives strict inequality. -/
Statement (m n : ℕ) (f : Fin m → Fin n)
    (hinj : Function.Injective f) (hnsurj : ¬Function.Surjective f) :
    m < n := by
  Hint "Start with the injection bound from Level 2: `card_le_of_injective`
  gives you `Fintype.card (Fin m) <= Fintype.card (Fin n)`."
  Hint (hidden := true) "Try:
  `have h_le := Fintype.card_le_of_injective f hinj`"
  have h_le := Fintype.card_le_of_injective f hinj
  Hint "Evaluate the cardinalities with `Fintype.card_fin` to get `m <= n`."
  Hint (hidden := true) "Try:
  `rw [Fintype.card_fin, Fintype.card_fin] at h_le`"
  rw [Fintype.card_fin, Fintype.card_fin] at h_le
  Hint "Now you need strict inequality `m < n`. You have `m <= n`.
  Use `apply lt_of_le_of_ne` to reduce this to proving `m != n`."
  Hint (hidden := true) "Try `apply lt_of_le_of_ne h_le`."
  apply lt_of_le_of_ne h_le
  Hint "The goal is `m != n`. Assume `heq : m = n` and derive `False`.
  Use `intro heq` to assume equality."
  Hint (hidden := true) "Try `intro heq`."
  intro heq
  Hint "Now `subst heq` replaces `n` with `m` everywhere. After this,
  `f` becomes `f : Fin m -> Fin m` -- an endofunction."
  Hint (hidden := true) "Try `subst heq`."
  subst heq
  Hint "For finite types, an injective endofunction is automatically
  surjective (`Finite.surjective_of_injective`). But `hnsurj` says
  `f` is NOT surjective. Apply the surjectivity to `hnsurj` to get
  `False`."
  Hint (hidden := true) "Try `exact hnsurj (Finite.surjective_of_injective hinj)`."
  exact hnsurj (Finite.surjective_of_injective hinj)

Conclusion "
Strict injection bound:
1. `card_le_of_injective f hinj` -- injection gives `m <= n`
2. `apply lt_of_le_of_ne h_le` -- reduce to proving `m != n`
3. `intro heq; subst heq` -- assume equality, make `f` an endofunction
4. `exact hnsurj (Finite.surjective_of_injective hinj)` -- contradiction

**The key insight**: For finite types, injectivity and surjectivity
are 'dual' -- an injective map between sets of equal size must be
surjective. So the only way an injection can fail to be surjective
is if the domain is *strictly smaller* than the codomain.

**Two roads to strict inequality**:

| Approach | Hypothesis | Tool |
|---|---|---|
| Subset (Level 6) | `s Subset t` (strict) | `card_lt_card` |
| Function (this level) | Injective + not Surjective | `card_le_of_injective` + `Finite.surjective_of_injective` |

These are the same mathematical fact viewed from two perspectives:
a strict subset gives a natural injection that misses an element
(hence is not surjective). And a non-surjective injection has an
image that is a strict subset of the codomain.
"

/-- `Finite.surjective_of_injective hinj` states that for finite
types, an injective function `f : alpha -> alpha` (endofunction)
is automatically surjective.

## Syntax
```
exact Finite.surjective_of_injective hinj
```

## When to use it
When you have an injective endofunction on a finite type and need
to derive surjectivity. Often used after `subst` makes two types
equal, turning `f : alpha -> beta` into `f : alpha -> alpha`.

## Why it works
A finite type has finitely many elements. An injection maps them
to distinct elements, so the image has the same cardinality as the
domain. Since domain = codomain (endofunction), the image fills
the entire codomain — surjectivity.
-/
TheoremDoc Finite.surjective_of_injective as "Finite.surjective_of_injective" in "Fintype"

/-- `lt_of_le_of_ne h_le h_ne` states that if `a <= b` and
`a != b`, then `a < b`.

## Syntax
```
apply lt_of_le_of_ne h_le
-- then prove a != b
```
or
```
exact lt_of_le_of_ne h_le h_ne
```

## When to use it
When you have `<=` and want `<`, and you can prove the two sides
are not equal. This is a common pattern: establish a weak bound,
then strengthen it by ruling out equality.
-/
TheoremDoc lt_of_le_of_ne as "lt_of_le_of_ne" in "Order"

TacticDoc subst "
`subst h` substitutes a hypothesis `h : a = b` into the goal
and context, replacing all occurrences of `b` with `a` (or vice
versa). The hypothesis `h` must equate a free variable.

## Example
If you have `heq : m = n` and `f : Fin m -> Fin n`, then
`subst heq` replaces `n` with `m` everywhere, making
`f : Fin m -> Fin m`.

## When to use it
When you want to unify two variables that are known to be equal,
simplifying the types in your context.
"

NewTheorem Finite.surjective_of_injective lt_of_le_of_ne

NewTactic subst

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
