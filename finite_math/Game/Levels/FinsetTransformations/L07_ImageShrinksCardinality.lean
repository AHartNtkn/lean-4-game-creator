import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 7

Title "Image can shrink cardinality"

Introduction
"
# Non-injective functions shrink the image

When we use `Finset.image` with a function that is **not** injective,
different inputs can produce the same output. Since finsets have no
duplicates, the image may have **fewer** elements than the source.

## Example

Consider `f(x) = x % 2` on {0, 1, 2, 3}:
- `f(0) = 0`, `f(1) = 1`, `f(2) = 0`, `f(3) = 1`

The image is {0, 1} -- only 2 elements, even though the source
has 4.

## The key lemma

```
Finset.card_image_le : (s.image f).card ≤ s.card
```

This says the image can only **shrink** (or stay the same), never
grow. The inequality is strict exactly when the function is
non-injective on `s`.

## Your task

Prove that `Finset.card_image_le` holds for `f(x) = x % 2` on
{0, 1, 2, 3}. That is, the image has at most as many elements as the
source.

**Strategy**: This follows directly from the general lemma
`Finset.card_image_le`.
"

/-- The image of {0, 1, 2, 3} under `x ↦ x % 2` has at most 4 elements. -/
Statement : (Finset.image (· % 2) ({0, 1, 2, 3} : Finset Nat)).card ≤
    ({0, 1, 2, 3} : Finset Nat).card := by
  Hint "This is a direct consequence of the general lemma
  `Finset.card_image_le`, which says that image never increases
  cardinality."
  Hint (hidden := true) "Use `exact Finset.card_image_le`."
  exact Finset.card_image_le

Conclusion
"
The proof was a single `exact` -- the general lemma does all the work.

But the interesting point is that this inequality is **strict**:
the image {0, 1} has only 2 elements while the source {0, 1, 2, 3}
has 4. The function `x % 2` sends both `0` and `2` to `0`, and both
`1` and `3` to `1`.

## When is cardinality preserved?

The lemma `Finset.card_image_of_injective` gives the other direction:

```
Function.Injective f → (s.image f).card = s.card
```

If `f` is injective, no collisions occur and the cardinality is preserved.
This is also why `Finset.map` (which requires injectivity) guarantees
`card_map : (s.map e).card = s.card`.

## Summary

| Function type | Cardinality of image |
|---------------|---------------------|
| Any function | `≤ s.card` (card_image_le) |
| Injective | `= s.card` (card_image_of_injective) |
| Non-injective | `< s.card` (strict; collisions reduce size) |
"

/-- `Finset.card_image_le` states that `(Finset.image f s).card ≤ s.card`.

The image of a finset under any function has at most as many elements
as the original finset. Duplicates in the output are removed, so a
non-injective function strictly reduces cardinality. -/
TheoremDoc Finset.card_image_le as "Finset.card_image_le" in "Finset"

/-- `Finset.card_image_of_injective` states that if `f` is injective,
then `(Finset.image f s).card = s.card`.

An injective function produces no duplicate outputs, so the image
has the same number of elements as the source. -/
TheoremDoc Finset.card_image_of_injective as "Finset.card_image_of_injective" in "Finset"

NewTheorem Finset.card_image_le Finset.card_image_of_injective
DisabledTactic trivial decide native_decide aesop simp_all
