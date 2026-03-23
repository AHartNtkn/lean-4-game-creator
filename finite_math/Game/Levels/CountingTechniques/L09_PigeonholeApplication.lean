import Game.Metadata

World "CountingTechniques"
Level 9

Title "Pigeonhole: Finding a Collision"

Introduction "
# Pigeonhole with Witnesses

Level 8 proved that `f : Fin 6 -> Fin 4` is *not injective*.
But 'not injective' is a negative statement — it says a collision
exists without telling you where.

The **constructive pigeonhole principle** gives you actual
witnesses: two distinct elements that map to the same value.

We use `Fintype.exists_ne_map_eq_of_card_lt`:

```
Fintype.exists_ne_map_eq_of_card_lt :
  (f : alpha -> beta) ->
  Fintype.card beta < Fintype.card alpha ->
  exists x y : alpha, x != y and f x = f y
```

This is cleaner than the Finset-level version — it works directly
with finite types, no extra conditions needed.

**Your task**: Given `f : Fin 5 -> Fin 2`, find two distinct
inputs that map to the same output.
"

/-- Among 5 elements mapping to 2 targets, two must collide. -/
Statement (f : Fin 5 → Fin 2) :
    ∃ a b : Fin 5, a ≠ b ∧ f a = f b := by
  Hint "Apply the constructive pigeonhole theorem.
  `Fintype.exists_ne_map_eq_of_card_lt` needs the function
  and a proof that `card (Fin 2) < card (Fin 5)`.

  **Common wrong approach**: If you try `not_injective_of_card_lt`
  from Level 8, you'll get `not Injective f` — a negative
  statement without witnesses. This level needs explicit
  witnesses `a` and `b`, so use the constructive version."
  Hint (hidden := true) "Try:
  `apply Fintype.exists_ne_map_eq_of_card_lt`"
  apply Fintype.exists_ne_map_eq_of_card_lt
  Hint "Now prove the cardinality comparison:
  `Fintype.card (Fin 2) < Fintype.card (Fin 5)`.
  Evaluate with `Fintype.card_fin` and close with `omega`."
  Hint (hidden := true) "Try:
  `rw [Fintype.card_fin, Fintype.card_fin]`"
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `2 < 5`. Try `omega`."
  omega

Conclusion "
The constructive pigeonhole in two steps:

1. `apply Fintype.exists_ne_map_eq_of_card_lt` — invoke the theorem
2. `rw [card_fin, card_fin]; omega` — verify `2 < 5`

Compare with Level 8:
- Level 8 (`not_injective_of_card_lt`): proves `not Injective f`
  — a *negative* statement
- Level 9 (`exists_ne_map_eq_of_card_lt`): proves
  `exists a b, a != b and f a = f b` — *constructive* witnesses

**When to reach for this**: When you need not just 'not injective'
but actual colliding elements. This is common in competition
problems: 'among $n+1$ integers, two share the same residue mod $n$'
is pigeonhole with the witness giving you the pair.

**In plain mathematics**: The statement 'there exist two distinct
elements with the same image' is stronger than 'the function is
not injective' — it gives constructive content that you can use
in subsequent proof steps.
"

/-- `Fintype.exists_ne_map_eq_of_card_lt f h` states that if
`Fintype.card beta < Fintype.card alpha`, then there exist
`x y : alpha` with `x != y` and `f x = f y`.

## Syntax
```
apply Fintype.exists_ne_map_eq_of_card_lt
-- then prove Fintype.card beta < Fintype.card alpha
```
or
```
have h := Fintype.exists_ne_map_eq_of_card_lt f hlt
obtain (a, b, hne, heq) := h
```

## When to use it
When you need explicit colliding elements from a function that
maps a larger type into a smaller one (constructive pigeonhole).
Unlike `not_injective_of_card_lt`, this gives witnesses.
-/
TheoremDoc Fintype.exists_ne_map_eq_of_card_lt as "Fintype.exists_ne_map_eq_of_card_lt" in "Fintype"

NewTheorem Fintype.exists_ne_map_eq_of_card_lt

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.exists_ne_map_eq_of_card_lt_of_maps_to
