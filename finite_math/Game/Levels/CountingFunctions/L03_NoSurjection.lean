import GameServer.Commands
import Mathlib

World "CountingFunctions"
Level 3

Title "No surjection from Fin 2 to Fin 3"

Introduction
"
# Which Functions Are Surjective?

Of the 9 functions from `Fin 2` to `Fin 3`, how many are
**surjective** (onto)? The answer is **zero**.

A surjective function must hit every element of the codomain. But
we only have 2 inputs and 3 outputs to cover. By the pigeonhole
principle in reverse: if the domain is smaller than the codomain,
surjectivity is impossible.

## The formal argument

If `f : Fin 2 → Fin 3` were surjective, then by
`Fintype.card_le_of_surjective`, we would have
`Fintype.card (Fin 3) ≤ Fintype.card (Fin 2)`, i.e., `3 ≤ 2`.
That is a contradiction.

## Your task

Prove that no function `f : Fin 2 → Fin 3` can be surjective.

This is the **reverse pigeonhole**: you used `Fintype.card_le_of_injective`
in the Counting and Pigeonhole world to show that injections require
the domain to be no larger than the codomain. Now use
`Fintype.card_le_of_surjective` to show that surjections require the
codomain to be no larger than the domain.
"

/-- No function from `Fin 2` to `Fin 3` can be surjective. -/
Statement (f : Fin 2 → Fin 3) : ¬ Function.Surjective f := by
  Hint "Start by assuming surjectivity for contradiction: `intro hsurj`."
  intro hsurj
  Hint "Now use `Fintype.card_le_of_surjective` to derive a cardinality
  bound. This lemma says: if `f` is surjective, then
  `Fintype.card (Fin 3) ≤ Fintype.card (Fin 2)`.

  Try `have h := Fintype.card_le_of_surjective f hsurj`."
  have h := Fintype.card_le_of_surjective f hsurj
  Hint "Now `h : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2)`.
  Rewrite the cardinalities using `Fintype.card_fin`."
  rw [Fintype.card_fin, Fintype.card_fin] at h
  Hint "Now `h : 3 ≤ 2`, which is false. Use `omega` to derive
  the contradiction."
  Hint (hidden := true) "Use `omega`. This closes the goal because
  `3 ≤ 2` contradicts arithmetic."
  omega

Conclusion
"
No function from `Fin 2` to `Fin 3` can be surjective.

The proof was a mirror of the pigeonhole argument:
1. Assume `f` is surjective.
2. Derive `|codomain| ≤ |domain|` from `Fintype.card_le_of_surjective`.
3. Evaluate: `3 ≤ 2`.
4. Contradiction.

## Pigeonhole and its dual

| Principle | Condition | Conclusion |
|-----------|-----------|------------|
| Pigeonhole | `|domain| > |codomain|` | No injection exists |
| Reverse pigeonhole | `|codomain| > |domain|` | No surjection exists |

Both are instances of the same counting idea: you cannot create a
perfect pairing between sets of different sizes. With too many inputs,
some must collide (no injection). With too few inputs, some outputs
must be missed (no surjection).

## Concretely

The 9 functions listed as $(f(0), f(1))$ are:

$(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)$

None of them hits all three outputs. For instance, $(0,1)$ misses `2`;
$(2,2)$ misses both `0` and `1`. With only 2 inputs, the image has at
most 2 elements, but the codomain has 3.

**In plain language**: \"A function from a 2-element set to a 3-element
set cannot be onto: there are not enough inputs to cover all outputs.\"
"

/-- `Fintype.card_le_of_surjective` states that a surjective function
from `α` to `β` implies `Fintype.card β ≤ Fintype.card α`:
```
Fintype.card_le_of_surjective (f : α → β) :
  Function.Surjective f → Fintype.card β ≤ Fintype.card α
```

**When to use**: In reverse-pigeonhole arguments. If
`Fintype.card β > Fintype.card α`, then no function `α → β` is
surjective. -/
TheoremDoc Fintype.card_le_of_surjective as "Fintype.card_le_of_surjective" in "Fintype"

NewTheorem Fintype.card_le_of_surjective
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide simp aesop simp_all
