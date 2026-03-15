import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 5

Title "`Finset.map` vs `Finset.image`"

Introduction
"
# `Finset.map`: image for injective functions

Mathlib provides two ways to apply a function to a finset:

| Operation | Input | Requirement |
|-----------|-------|-------------|
| `Finset.image f s` | `f : α → β` | `DecidableEq β` |
| `Finset.map e s` | `e : α ↪ β` | `e` is an **embedding** (injective function with proof) |

An **embedding** `α ↪ β` bundles a function with a proof of
injectivity. Lean writes it as `⟨f, hf⟩` where `f` is the function
and `hf` is the injectivity proof.

## Why does `map` exist?

Because `map` **knows** the function is injective, it can guarantee
that the output has the same cardinality as the input. The key lemma
is:

```
Finset.card_map : (s.map e).card = s.card
```

For `image`, we only get the weaker `Finset.card_image_le`:
`(s.image f).card ≤ s.card`.

## Membership in `map`

```
Finset.mem_map : b ∈ s.map e ↔ ∃ a ∈ s, e a = b
```

This looks identical to `mem_image` -- the proof shape is the same.
The difference is behind the scenes: `map` uses the embedding's
injectivity to maintain the `Nodup` invariant more efficiently.

## Your task

Prove that `4` belongs to the image of {1, 2, 3} under the
successor embedding `⟨Nat.succ, Nat.succ_injective⟩`.
"

/-- `4` belongs to the map of {1, 2, 3} under the successor embedding. -/
Statement : (4 : Nat) ∈ Finset.map ⟨Nat.succ, Nat.succ_injective⟩ ({1, 2, 3} : Finset Nat) := by
  Hint "The goal asks about `Finset.map`. Rewrite with `Finset.mem_map`
  to expose the existential -- just like `Finset.mem_image`."
  Hint (hidden := true) "Use `rw [Finset.mem_map]`."
  rw [Finset.mem_map]
  Hint "Provide the witness. Which element of the source finset has
  successor `4`?"
  Hint (hidden := true) "Use `use 3`."
  use 3
  Hint "Prove the conjunction: `3` is in the source finset and
  `Nat.succ 3 = 4`."
  Hint (hidden := true) "Use `constructor`, then
  `simp [Finset.mem_insert, Finset.mem_singleton]` and `rfl`."
  constructor
  · simp [Finset.mem_insert, Finset.mem_singleton]
  · rfl

Conclusion
"
The proof was nearly identical to an `image` proof. The difference
between `map` and `image` is not in **how you prove membership**
but in **what guarantees you get**:

## `map` vs. `image` summary

| | `image` | `map` |
|---|---------|-------|
| Input function | any `f : α → β` | embedding `e : α ↪ β` |
| Cardinality | `(s.image f).card ≤ s.card` | `(s.map e).card = s.card` |
| Membership proof | existential witness | existential witness |
| When to use | general functions | when injectivity matters |

**Rule of thumb**: Use `image` for general computations. Use `map`
when you need to preserve cardinality.

In the rest of this world, we will work primarily with `image` since
it is more general and more commonly needed.
"

/-- `Finset.mem_map` states that
`b ∈ Finset.map e s ↔ ∃ a ∈ s, e a = b`.

Membership in a mapped finset is proved by providing a witness, just
like `Finset.mem_image`. The difference is that `map` requires an
embedding (injective function). -/
TheoremDoc Finset.mem_map as "Finset.mem_map" in "Finset"

/-- `Finset.card_map` states that `(s.map e).card = s.card`.

Because `map` uses an injective function, the output finset has
exactly as many elements as the input. This is stronger than
`card_image_le`, which only gives `≤`. -/
TheoremDoc Finset.card_map as "Finset.card_map" in "Finset"

/-- `Finset.map e s` applies the embedding `e : α ↪ β` to every element
of `s`, producing a finset of the same cardinality.

An embedding `α ↪ β` is a pair `⟨f, hf⟩` where `f : α → β` and
`hf : Function.Injective f`.

Use `Finset.mem_map` for membership and `Finset.card_map` for
cardinality. -/
DefinitionDoc Finset.map as "Finset.map"

NewTheorem Finset.mem_map Finset.card_map
NewDefinition Finset.map
DisabledTactic trivial decide native_decide aesop simp_all
