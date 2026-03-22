import Game.Metadata

World "Fintype"
Level 13

Title "Producing an Equiv"

Introduction "
# Where Do Equivalences Come From?

In the last two levels, you received an `Equiv` as a hypothesis
(`e : α ≃ ...`) and used `card_congr e`. But equivalences don't
appear from nowhere — they're constructed!

Lean's library provides **combinators** for building equivalences
from simpler ones. One of the most useful is:

```
Equiv.prodComm α β : α × β ≃ β × α
```

This says: swapping the components of a pair is a bijection. The
forward map sends `(a, b)` to `(b, a)`, the inverse sends `(b, a)`
back to `(a, b)`, and both compositions are the identity.

**Your task**: Prove that `α × β` and `β × α` have the same
cardinality by producing the equivalence yourself. No `e` hypothesis
is given — you must construct the `Equiv` using `Equiv.prodComm`
and feed it to `Fintype.card_congr`.
"

/-- The product α × β has the same cardinality as β × α. -/
Statement (α β : Type*) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card (β × α) := by
  Hint "You need to produce an equivalence `α × β ≃ β × α` and feed it
  to `Fintype.card_congr`. The library combinator `Equiv.prodComm α β`
  gives exactly this equivalence."
  Hint (hidden := true) "Try `exact Fintype.card_congr (Equiv.prodComm α β)`."
  exact Fintype.card_congr (Equiv.prodComm α β)

Conclusion "
You **produced** an equivalence instead of receiving one as a hypothesis.
This is the key insight: `Fintype.card_congr` works with any `Equiv`,
whether given to you or constructed on the spot.

The library provides many useful combinators:

| Combinator | Equivalence |
|---|---|
| `Equiv.prodComm α β` | `α × β ≃ β × α` |
| `Equiv.sumComm α β` | `α ⊕ β ≃ β ⊕ α` |
| `Equiv.prodAssoc α β γ` | `(α × β) × γ ≃ α × (β × γ)` |
| `Equiv.sumAssoc α β γ` | `(α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ)` |

In later worlds, you'll construct more complex equivalences to count
combinatorial objects. For now, the pattern is: **find or build an
Equiv, then apply card_congr**.

Next: a concrete computation that puts all the tools together.
"

/-- `Equiv.prodComm α β` is the equivalence `α × β ≃ β × α` that swaps
the components of a pair: `(a, b) ↦ (b, a)`.

## Syntax
```
Equiv.prodComm α β    -- produces α × β ≃ β × α
```

## When to use it
When you need to show that `α × β` and `β × α` have the same
cardinality, or when you need to commute a product type to match
a target expression.

## Related combinators
- `Equiv.sumComm α β : α ⊕ β ≃ β ⊕ α` — commutes sum types
- `Equiv.prodAssoc α β γ : (α × β) × γ ≃ α × (β × γ)` — associates products
-/
DefinitionDoc Equiv.prodComm as "Equiv.prodComm"

NewDefinition Equiv.prodComm

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf

DisabledTheorem Nat.mul_comm mul_comm
