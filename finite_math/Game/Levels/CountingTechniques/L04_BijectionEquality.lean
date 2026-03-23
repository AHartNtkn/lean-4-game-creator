import Game.Metadata

World "CountingTechniques"
Level 4

Title "Bijection = Injection + Surjection"

Introduction "
# Two Inequalities Make an Equality

Levels 2 and 3 gave you:
- Injective `f : α → β` implies `|α| ≤ |β|`
- Surjective `f : α → β` implies `|β| ≤ |α|`

If `f` is **both** injective and surjective (a bijection), you
get both inequalities simultaneously. And two opposing inequalities
give **equality** via `le_antisymm`:

```
le_antisymm : a ≤ b → b ≤ a → a = b
```

This derives the bijection principle `|α| = |β|` from the two
one-directional bounds — showing that bijective counting is not
a separate axiom but a *consequence* of injection and surjection
bounds.

**Your task**: Given `f : α → β` that is both injective and
surjective, prove `Fintype.card α = Fintype.card β` using
`le_antisymm` with the two bounds.
"

/-- Injective + surjective implies equal cardinality. -/
Statement (α β : Type*) [Fintype α] [Fintype β] (f : α → β)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    Fintype.card α = Fintype.card β := by
  Hint "To prove equality from two inequalities, use `le_antisymm`.
  This creates two subgoals: `|α| ≤ |β|` and `|β| ≤ |α|`."
  Hint (hidden := true) "Try `apply le_antisymm`."
  apply le_antisymm
  Hint "The first goal `Fintype.card α ≤ Fintype.card β` follows
  from injectivity — you proved this pattern in Level 2."
  Hint (hidden := true) "Try
  `exact Fintype.card_le_of_injective f hinj`."
  · exact Fintype.card_le_of_injective f hinj
  Hint "The second goal `Fintype.card β ≤ Fintype.card α` follows
  from surjectivity — you proved this pattern in Level 3."
  Hint (hidden := true) "Try
  `exact Fintype.card_le_of_surjective f hsurj`."
  · exact Fintype.card_le_of_surjective f hsurj

Conclusion "
The bijection principle derived in three steps:
1. `apply le_antisymm` — reduce equality to two inequalities
2. `exact Fintype.card_le_of_injective f hinj` — the `≤` direction
3. `exact Fintype.card_le_of_surjective f hsurj` — the `≥` direction

**The deep insight**: You've just proved that bijective counting is
a **theorem**, not an axiom. The Bijection Principle ('bijective
functions preserve cardinality') follows from two simpler facts:
injections can't increase size, and surjections can't decrease it.
Together, they force equality. This is a genuine mathematical
insight about the *structure* of counting.

**The meta-lesson**: `le_antisymm` is a general proof strategy
for showing equality. Whenever you need `a = b` for ordered
quantities, consider proving both `a ≤ b` and `b ≤ a` separately.
This works in many contexts beyond cardinality.

**Connecting back to Level 1**: Level 1 used `card_congr` with an
`Equiv` (explicit bijection) to transfer cardinality. This level
shows the same result follows from injectivity + surjectivity
without constructing an explicit `Equiv`. Both approaches are
useful: `card_congr` when you have a natural bijection,
`le_antisymm` when you have separate injection/surjection proofs.
"

/-- `le_antisymm` states that if `a ≤ b` and `b ≤ a`, then `a = b`.

## Syntax
```
apply le_antisymm
-- subgoal 1: a ≤ b
-- subgoal 2: b ≤ a
```

## When to use it
When you want to prove equality of ordered quantities by showing
both `≤` and `≥`. This is the standard 'sandwich' argument.

## Example
To prove `Fintype.card α = Fintype.card β`:
```
apply le_antisymm
· -- prove card α ≤ card β (e.g. via injection)
· -- prove card β ≤ card α (e.g. via surjection)
```
-/
TheoremDoc le_antisymm as "le_antisymm" in "Order"

NewTheorem le_antisymm

/-- `Fintype.card_of_bijective hbij` states that if `f : alpha -> beta`
is bijective (both injective and surjective), then
`Fintype.card alpha = Fintype.card beta`.

## Syntax
```
exact Fintype.card_of_bijective hbij
```

## When to use it
When you already have `Function.Bijective f` as a single hypothesis.
If you have `Injective f` and `Surjective f` separately, the
`le_antisymm` approach from this level is more direct.

## Why it's disabled here
This level teaches you to derive the bijection principle from
injection and surjection bounds. `card_of_bijective` would skip
the derivation.
-/
TheoremDoc Fintype.card_of_bijective as "Fintype.card_of_bijective" in "Fintype"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
-- Prevent bypassing via Equiv construction or bijective one-shot
DisabledTheorem Fintype.card_congr Equiv.ofBijective Fintype.card_of_bijective
