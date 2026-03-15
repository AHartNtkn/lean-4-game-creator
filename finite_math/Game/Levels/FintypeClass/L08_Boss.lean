import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 8

Title "Boss: Cardinality of Fin 2 × Bool"

Introduction
"
# Boss: Computing `Fintype.card` for a compound type

Time to integrate everything from this world. Prove that the type
`Fin 2 × Bool` has exactly 4 elements.

## What you need

This requires combining three lemmas:
1. `Fintype.card_prod` to split the product cardinality.
2. `Fintype.card_fin` to evaluate `Fintype.card (Fin 2)`.
3. `Fintype.card_bool` to evaluate `Fintype.card Bool`.

All three were introduced and practiced in earlier levels of this world.
The challenge is chaining them together in the right order.
"

/-- `Fin 2 × Bool` has exactly 4 elements. -/
Statement : Fintype.card (Fin 2 × Bool) = 4 := by
  Hint "Start by splitting the product cardinality. Which lemma expresses
  `Fintype.card (α × β)` in terms of `Fintype.card α` and `Fintype.card β`?"
  Hint (hidden := true) "Use `rw [Fintype.card_prod]` to get
  `Fintype.card (Fin 2) * Fintype.card Bool = 4`."
  rw [Fintype.card_prod]
  Hint "Now simplify each factor. Use `Fintype.card_fin` for `Fin 2`
  and `Fintype.card_bool` for `Bool`."
  Hint (hidden := true) "Use `rw [Fintype.card_fin, Fintype.card_bool]`."
  rw [Fintype.card_fin, Fintype.card_bool]

Conclusion
"
Congratulations on completing the Fintype world!

You proved `Fintype.card (Fin 2 × Bool) = 4` by decomposing the product:
`Fintype.card (Fin 2) * Fintype.card Bool = 2 * 2 = 4`.

## What you learned in this world

| Concept | Level | Key item |
|---------|-------|----------|
| `Fintype` definition | L01 | `Fintype`, `Finset.univ` |
| Universal membership | L02 | `Finset.mem_univ` |
| Counting bridge | L03 | `Finset.card_univ` |
| `Fin n` cardinality | L04 | `Fintype.card_fin` |
| `Bool` cardinality | L05 | `Fintype.card_bool` |
| Product cardinality | L06 | `Fintype.card_prod` |
| Infinite types | L07 | `Nat` has no `Fintype` |
| Integration | L08 | All of the above |

## Transfer moment

In ordinary mathematics, to count the elements of a finite set, you
list them all and count. The `Fintype` class formalizes this: it provides
the list (`Finset.univ`) and the count (`Fintype.card`).

The cardinality rules you used are the formal versions of basic counting
principles:
- **The set $\\{0, \\ldots, n-1\\}$ has $n$ elements** (`Fintype.card_fin`).
- **$|A \\times B| = |A| \\cdot |B|$** (`Fintype.card_prod`).
- **Infinite sets cannot be listed** (no `Fintype Nat`).

## What comes next

The next world builds on `Fintype` to develop more counting results:
cardinalities of sum types, function types, and subtypes, leading to
the pigeonhole principle.
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
