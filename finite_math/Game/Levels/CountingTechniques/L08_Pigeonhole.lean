import Game.Metadata

World "CountingTechniques"
Level 8

Title "The Pigeonhole Principle"

Introduction "
# Technique 3: The Pigeonhole Principle

If you have 6 pigeons and only 4 holes, no matter how you assign
pigeons to holes, some hole must contain at least 2 pigeons.
Equivalently: no injective function from a larger set to a smaller
set exists.

The formal statement is `Fintype.not_injective_of_card_lt`:

```
Fintype.not_injective_of_card_lt :
  (f : α → β) → Fintype.card β < Fintype.card α →
  ¬Function.Injective f
```

Read it as: if the target has fewer elements than the source,
then `f` cannot be injective — some two inputs must collide.

Notice the connection to Level 2: the injection bound says
`Injective f -> card alpha <= card beta`. Taking the contrapositive:
`card beta < card alpha -> not Injective f`. That's exactly
the pigeonhole principle! Pigeonhole is the **contrapositive**
of the injection bound — the same principle read backwards.

You proved a concrete version of this in the Cardinality world
(Levels 22-23) using `card_image_of_injective` and `card_le_card`.
Now use the direct pigeonhole theorem.

**About `omega`**: After evaluating `card_fin`, you'll have a
concrete arithmetic goal like `4 < 6`. The `omega` tactic
(introduced in the MeetFin world) closes goals about natural
number arithmetic automatically. It handles `<`, `<=`, `=`,
and linear combinations.

**Your task**: Prove that no function from `Fin 6` to `Fin 4`
is injective.
"

/-- No function from Fin 6 to Fin 4 is injective. -/
Statement (f : Fin 6 → Fin 4) : ¬Function.Injective f := by
  Hint "Apply `Fintype.not_injective_of_card_lt` to reduce the goal
  to a cardinality comparison."
  Hint (hidden := true) "Try `apply Fintype.not_injective_of_card_lt`."
  apply Fintype.not_injective_of_card_lt
  Hint "The goal is `Fintype.card (Fin 4) < Fintype.card (Fin 6)`.
  Evaluate using `Fintype.card_fin` and close with `omega`."
  Hint (hidden := true) "Try
  `rw [Fintype.card_fin, Fintype.card_fin]` then `omega`."
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `4 < 6`. Try `omega`."
  omega

Conclusion "
The pigeonhole principle in three steps:
1. `apply Fintype.not_injective_of_card_lt` — reduce to a size
   comparison
2. `rw [Fintype.card_fin, ...]` — evaluate the cardinalities
3. The arithmetic is trivially `4 < 6`

**Why this is powerful**: The Cardinality world's proof of
pigeonhole (Levels 22-23) required 4 steps: assume injective,
compute image size, bound image size, derive contradiction.
`not_injective_of_card_lt` packages all of that into a single
theorem. The work shifts to establishing `card beta < card alpha`.

**Pigeonhole = contrapositive of injection bound**: Level 2 said
`Injective f -> |alpha| <= |beta|`. The contrapositive is
`|beta| < |alpha| -> not Injective f` — exactly what you just proved.
Pigeonhole is not a separate principle; it's the injection bound
read backwards.

**In plain mathematics**: The Pigeonhole Principle (also called
the Dirichlet Box Principle) states:

> If $n$ items are placed into $m$ containers and $n > m$, then
> at least one container holds more than one item.

The contrapositive is often more useful in proofs: if every
container holds at most one item (injectivity), then the number
of items can't exceed the number of containers ($n \\leq m$).

**The counting contradiction pattern**: This is the same proof
strategy from Level 5: assume a function property, derive a
numerical bound, show the bound is absurd. Level 5 used the
surjection bound to get `5 <= 3`; this level uses the injection
bound to get `|source| <= |target|` when `|target| < |source|`.
Watch for this pattern — you'll use it again in the double
counting section.

**Generalized pigeonhole**: The full version strengthens this: if
$n$ items are placed into $m$ containers, some container holds at
least $\\lceil n/m \\rceil$ items. The version we proved here is the
special case where $\\lceil n/m \\rceil \\geq 2$ (i.e., $n > m$).
"

/-- `Fintype.not_injective_of_card_lt f hlt` states that if
`Fintype.card β < Fintype.card α`, then `f : α → β` is not
injective.

## Syntax
```
apply Fintype.not_injective_of_card_lt
-- then prove Fintype.card β < Fintype.card α
```
or
```
exact Fintype.not_injective_of_card_lt f hlt
```

## When to use it
When you need to show a function isn't injective by comparing
the sizes of source and target types. The target must be
strictly smaller than the source.

## Example
```
-- f : Fin 10 → Fin 7
apply Fintype.not_injective_of_card_lt
rw [Fintype.card_fin, Fintype.card_fin]
-- goal: 7 < 10
```
-/
TheoremDoc Fintype.not_injective_of_card_lt as "Fintype.not_injective_of_card_lt" in "Fintype"

NewTheorem Fintype.not_injective_of_card_lt

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
