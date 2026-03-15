import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 3

Title "Mapping a function over a finset"

Introduction
"
# `Finset.image`: applying a function to every element

While `filter` selects elements, `Finset.image` **transforms** them.
Given a function `f : α → β` and a finset `s : Finset α`, the
expression `Finset.image f s` is the finset of all outputs of `f` on
elements of `s`.

The key membership lemma is:

```
Finset.mem_image : b ∈ Finset.image f s ↔ ∃ a ∈ s, f a = b
```

An element `b` belongs to the image exactly when there is **some**
element `a ∈ s` with `f a = b`. This is an **existential**: you need
a witness.

## Important difference from `filter`

- `mem_filter` produces a **conjunction** (`∧`): membership and predicate.
- `mem_image` produces an **existential** (`∃`): a witness and a proof.

These are fundamentally different proof obligations.

## Your task

Prove that `6` belongs to the image of {1, 2, 3} under the doubling
function `(· * 2)`.

**Strategy**: Rewrite with `Finset.mem_image`, then provide the
witness `3` (since `3 * 2 = 6`).
"

/-- `6` belongs to the image of `{1, 2, 3}` under doubling. -/
Statement : (6 : Nat) ∈ Finset.image (· * 2) ({1, 2, 3} : Finset Nat) := by
  Hint "The goal asks whether `6` is in the image under the doubling
  function. Rewrite with `Finset.mem_image` to see the existential."
  Hint (hidden := true) "Use `rw [Finset.mem_image]`."
  rw [Finset.mem_image]
  Hint "The goal is now an existential: you need to provide an element
  from the source finset that doubles to `6`."
  Hint (hidden := true) "Use `use 3`."
  use 3
  Hint "Now you need to show that `3` is in the source finset and that
  `3 * 2 = 6`. Split with `constructor` and close each part."
  Hint (hidden := true) "Use `constructor` then
  `simp [Finset.mem_insert, Finset.mem_singleton]` and `rfl`."
  constructor
  · simp [Finset.mem_insert, Finset.mem_singleton]
  · rfl

Conclusion
"
You proved your first image membership fact. The proof shape is
different from filter membership:

1. **Rewrite** with `Finset.mem_image` to expose the existential.
2. **Provide a witness** with `use` (here, `use 3`).
3. **Prove two things**: the witness is in the source finset, and
   applying the function gives the target value.

## Filter vs. Image: proof shapes

| Operation | `mem_...` gives | You need to provide |
|-----------|----------------|---------------------|
| `filter`  | `a ∈ s ∧ p a`  | Membership + predicate |
| `image`   | `∃ a ∈ s, f a = b` | A **witness** + membership + equation |

The existential in `mem_image` is the key new ingredient.
"

/-- `Finset.mem_image` states that
`b ∈ Finset.image f s ↔ ∃ a ∈ s, f a = b`.

An element belongs to the image finset exactly when some element of the
source finset maps to it. Use `rw [Finset.mem_image]` to expose the
existential, then `use` to provide the witness. -/
TheoremDoc Finset.mem_image as "Finset.mem_image" in "Finset"

/-- `Finset.image f s` is the finset of all values `f a` as `a` ranges
over `s`.

Given a function `f : α → β` (with `DecidableEq β`) and a finset
`s : Finset α`, `Finset.image f s` collects the outputs. Duplicates
in the output are removed.

Use `Finset.mem_image` to reason about membership. -/
DefinitionDoc Finset.image as "Finset.image"

NewTheorem Finset.mem_image
NewDefinition Finset.image
DisabledTactic trivial decide native_decide aesop simp_all
