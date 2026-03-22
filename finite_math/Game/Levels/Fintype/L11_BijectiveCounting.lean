import Game.Metadata

World "Fintype"
Level 11

Title "Bijective Counting"

Introduction "
# Counting via Equivalence

If two types `α` and `β` are in bijection — meaning there exists an
`Equiv` (written `α ≃ β`, typed `\\simeq`) — then they must have the
same number of elements. The theorem `Fintype.card_congr` captures this:

```
Fintype.card_congr : α ≃ β → Fintype.card α = Fintype.card β
```

Given an equivalence `e : α ≃ β`, the proof `Fintype.card_congr e`
produces the equation `Fintype.card α = Fintype.card β`.

An `Equiv` is a bijection with four fields: the forward map (`toFun`),
the inverse map (`invFun`), and proofs that they compose to the
identity in both directions (`left_inv`, `right_inv`). Think of
`α ≃ β` as saying: there's a perfect pairing between the elements
of `α` and the elements of `β`.

This is the formal version of **bijective counting**: to count the
elements of a complicated type, find a bijection to a simpler type
and count that instead.

**Your task**: Given an equivalence `e : α ≃ Fin 6`, prove that
`α` has 6 elements. Use `Fintype.card_congr` to transfer the
cardinality, then `Fintype.card_fin` to evaluate.
"

/-- If α is equivalent to Fin 6, then α has 6 elements. -/
Statement (α : Type*) [Fintype α] (e : α ≃ Fin 6) :
    Fintype.card α = 6 := by
  Hint "Use `rw [Fintype.card_congr e]` to replace `Fintype.card α`
  with `Fintype.card (Fin 6)`, then `rw [Fintype.card_fin]` to evaluate."
  Hint (hidden := true) "Try `rw [Fintype.card_congr e, Fintype.card_fin]`."
  rw [Fintype.card_congr e, Fintype.card_fin]

Conclusion "
Bijective counting in two steps:

1. `rw [Fintype.card_congr e]` — transfer via the equivalence
2. `rw [Fintype.card_fin]` — evaluate the known cardinality

This is the **strongest counting tool**: if you can exhibit a bijection,
the cardinality follows automatically. You don't need to enumerate
elements or verify arithmetic — the bijection does all the work.

In mathematics, this is the statement: *equipotent sets have the same
cardinality*. In Lean, `Equiv` makes the bijection explicit and
machine-checkable.

Next: a coached practice combining `card_congr` with `card_prod`.
"

/-- An `Equiv` (written `α ≃ β`, typed `\\simeq`) is a bijection between
two types. It consists of four components:
- `toFun : α → β` — the forward map
- `invFun : β → α` — the inverse map
- `left_inv` — proof that `invFun ∘ toFun = id`
- `right_inv` — proof that `toFun ∘ invFun = id`

## When you see it
When a hypothesis says `e : α ≃ β`, it means `α` and `β` are in
bijection. You can use `Fintype.card_congr e` to conclude they have
the same cardinality.

## Notation
`α ≃ β` is typed as `\simeq`.
-/
DefinitionDoc Equiv as "Equiv"

/-- `Fintype.card_congr e` states that if `e : α ≃ β` is an equivalence,
then `Fintype.card α = Fintype.card β`.

## Syntax
```
rw [Fintype.card_congr e]     -- replaces card α with card β
exact Fintype.card_congr e    -- if the goal is card α = card β
```

## When to use it
When you have an equivalence `e : α ≃ β` and need to show that `α` and
`β` have the same cardinality. This is the formal version of bijective
counting.

## Example
Given `e : MyType ≃ Fin 10`, then `Fintype.card_congr e` proves
`Fintype.card MyType = Fintype.card (Fin 10)`.
-/
TheoremDoc Fintype.card_congr as "Fintype.card_congr" in "Fintype"

NewDefinition Equiv
NewTheorem Fintype.card_congr

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
