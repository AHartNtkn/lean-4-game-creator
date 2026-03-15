import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 6

Title "The pigeonhole principle (specific case)"

Introduction
"
# The Pigeonhole Principle

The **pigeonhole principle** is one of the most powerful and intuitive
counting arguments in mathematics:

> If you put $n + 1$ pigeons into $n$ holes, at least two pigeons must
> share a hole.

In Lean, a \"placement of pigeons into holes\" is a function. If we place
4 objects into 3 slots, the function `f : Fin 4 → Fin 3` cannot be
injective --- some two inputs must map to the same output.

## The proof strategy

To show `¬ Function.Injective f`:
1. **Assume** `f` is injective (proof by contradiction via `intro`).
2. **Derive a cardinality inequality**: if `f` is injective, then
   `Fintype.card (Fin 4) ≤ Fintype.card (Fin 3)`, using
   `Fintype.card_le_of_injective`.
3. **Evaluate** the cardinalities: this gives `4 ≤ 3`.
4. **Contradiction**: `4 ≤ 3` is false.

## Your task

Prove that no function from `Fin 4` to `Fin 3` is injective.
"

/-- No function from `Fin 4` to `Fin 3` can be injective. -/
Statement (f : Fin 4 → Fin 3) : ¬ Function.Injective f := by
  Hint "Start with `intro hinj` to assume `f` is injective and derive
  a contradiction."
  intro hinj
  Hint "Now use `Fintype.card_le_of_injective` to derive a cardinality
  bound from injectivity. This lemma says:
  ```
  Fintype.card_le_of_injective : Function.Injective f →
    Fintype.card α ≤ Fintype.card β
  ```
  Use `have h := Fintype.card_le_of_injective f hinj` to get the bound."
  have h := Fintype.card_le_of_injective f hinj
  Hint "Now `h : Fintype.card (Fin 4) ≤ Fintype.card (Fin 3)`.
  Rewrite both cardinalities using `Fintype.card_fin`.
  Try `rw [Fintype.card_fin, Fintype.card_fin] at h`."
  rw [Fintype.card_fin, Fintype.card_fin] at h
  Hint "Now `h : 4 ≤ 3`, which is false. Use `omega` to derive the
  contradiction."
  Hint (hidden := true) "Use `omega`. This tactic handles linear
  arithmetic contradictions."
  omega

Conclusion
"
You just proved your first pigeonhole result!

The proof followed the classic pattern:
1. Assume injectivity.
2. Derive `|domain| ≤ |codomain|` from `Fintype.card_le_of_injective`.
3. Evaluate the cardinalities.
4. Reach a contradiction (`4 ≤ 3`).

## The key lemma

`Fintype.card_le_of_injective` is the formal engine behind pigeonhole.
If `f : α → β` is injective, then `|α| ≤ |β|` --- each element of `α`
maps to a *distinct* element of `β`, so there must be at least as many
elements in `β`.

The contrapositive gives pigeonhole: if `|α| > |β|`, then `f` cannot
be injective.

**In plain language**: \"If you have 4 items and only 3 boxes, at least
two items must share a box.\"
"

/-- `Function.Injective f` means `f` maps distinct inputs to distinct
outputs: `∀ a b, f a = f b → a = b`.

A function is injective if and only if it is \"one-to-one.\"

**When to use**: When reasoning about functions that preserve
distinctness, or when applying the pigeonhole principle
(the contrapositive of injectivity + cardinality). -/
DefinitionDoc Function.Injective as "Function.Injective"

/-- `Fintype.card_le_of_injective` states that an injective function
from `α` to `β` implies `Fintype.card α ≤ Fintype.card β`:
```
Fintype.card_le_of_injective (f : α → β) :
  Function.Injective f → Fintype.card α ≤ Fintype.card β
```

**When to use**: In pigeonhole-style arguments. If you can show
`Fintype.card α > Fintype.card β`, then no function `α → β` is
injective. -/
TheoremDoc Fintype.card_le_of_injective as "Fintype.card_le_of_injective" in "Fintype"

NewTheorem Fintype.card_le_of_injective
NewDefinition Function.Injective
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
