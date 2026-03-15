import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 8

Title "Boss: Filter-image reasoning"

Introduction
"
# Boss: Combining filter and image

Time to integrate everything from this world. You will prove a result
that chains `image` and `filter` together and requires unpacking both.

## The statement

Given `s = {1, 2, 3, 4, 5}`:

- Filter `s` to keep elements greater than `3`: {4, 5}.
- Apply `(· + 1)` to the result: {5, 6}.

Prove two things:
1. **Part A**: Every element of this image-of-filter belongs to
   {1, 2, 3, 4, 5, 6} filtered by `(· > 4)`.
2. **Part B**: The image has at most as many elements as the filter
   (the `card_image_le` fact from L07).

## Proof plan

Split the conjunction, then:
- **Part A**: Introduce `x` and the hypothesis `hx`, unpack using
  `mem_image` and `mem_filter`, then build the target membership.
- **Part B**: Apply `Finset.card_image_le` directly.

This boss integrates membership reasoning AND cardinality reasoning.
"

/-- If `x` is in the image of the elements greater than 3 under `(· + 1)`,
then `x` is among the elements greater than 4 in the extended range.
Also, the image-of-filter has at most as many elements as the filter. -/
Statement : (∀ x, x ∈ Finset.image (· + 1)
    (Finset.filter (· > 3) ({1, 2, 3, 4, 5} : Finset Nat)) →
    x ∈ Finset.filter (· > 4) ({1, 2, 3, 4, 5, 6} : Finset Nat)) ∧
    (Finset.image (· + 1) (Finset.filter (· > 3) ({1, 2, 3, 4, 5} : Finset Nat))).card ≤
    (Finset.filter (· > 3) ({1, 2, 3, 4, 5} : Finset Nat)).card := by
  Hint "The goal is a conjunction. Split it with `constructor`."
  constructor
  · Hint "Start by introducing `x` and the hypothesis."
    Hint (hidden := true) "Use `intro x hx`."
    intro x hx
    Hint "The hypothesis `hx` says `x` is in an image. Use
    `Finset.mem_image` to expose the existential."
    Hint (hidden := true) "Use `rw [Finset.mem_image] at hx`."
    rw [Finset.mem_image] at hx
    Hint "Now `hx` is an existential: there exists some `a` in the filtered
    finset with `a + 1 = x`. Extract the witness and its properties."
    Hint (hidden := true) "Use `rcases hx with ⟨a, ha, rfl⟩`. The `rfl`
    substitutes `a + 1` for `x` everywhere."
    rcases hx with ⟨a, ha, rfl⟩
    Hint "Now the goal involves `a + 1` instead of `x`. The hypothesis
    `ha` says `a` is in the filtered finset. Unpack it with
    `Finset.mem_filter`."
    Hint (hidden := true) "Use `rw [Finset.mem_filter] at ha`."
    rw [Finset.mem_filter] at ha
    Hint "Now `ha` is a conjunction: `a` is in the source finset and
    `a > 3`. Extract both parts."
    Hint (hidden := true) "Use `rcases ha with ⟨hmem, hgt⟩`."
    rcases ha with ⟨hmem, hgt⟩
    Hint "The goal asks for `a + 1` to be in the target filtered finset.
    Rewrite the goal with `Finset.mem_filter` to split into membership
    and predicate."
    Hint (hidden := true) "Use `rw [Finset.mem_filter]`."
    rw [Finset.mem_filter]
    Hint "Now you need two things: `a + 1` is in the target finset, and
    `a + 1 > 4`. Since `a > 3` (from `hgt`), the arithmetic follows.

    Use `constructor` and handle each part."
    Hint (hidden := true) "Use `constructor`. For the first part:
    `simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢` then `omega`.
    For the second: `omega`."
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      omega
    · omega
  · Hint "**Part B**: The goal is a cardinality inequality:
    `(image (· + 1) (filter (· > 3) s)).card ≤ (filter (· > 3) s).card`.
    This is an instance of the general fact that image can only shrink
    (or maintain) cardinality. What lemma from Level 7 gives this?"
    Hint (hidden := true) "Use `exact Finset.card_image_le`."
    exact Finset.card_image_le

Conclusion
"
Congratulations on completing the Finset Transformations world!

You proved two things about the image of a filtered finset:

**Part A** (membership containment): Filtering then shifting preserves
a \"bigness\" property. The proof integrated:

- **`Finset.mem_image`** -- unpacking the image existential (L03-L04)
- **`Finset.mem_filter`** -- unpacking filter membership (L01-L02)
- **`rcases`** -- extracting components from existentials and
  conjunctions (from W6/W7)
- **`rfl` substitution** -- using `rcases ... with ⟨a, ha, rfl⟩` to
  substitute `f a` for the target variable
- **`omega`** -- arithmetic reasoning (from W1)

**Part B** (cardinality bound): The image of a filtered finset has at
most as many elements as the filtered finset. This used
`Finset.card_image_le` (L07).

## The `rfl` substitution trick

The pattern `rcases hx with ⟨a, ha, rfl⟩` is especially powerful for
image reasoning. When `hx : ∃ a ∈ s, f a = x`, using `rfl` for the
equation part substitutes `f a` for `x` everywhere in the goal. This
avoids having to manually rewrite with the equation.

## Transfer to ordinary mathematics

In a paper proof, you would write:

> \"Let x ∈ image (· + 1) (filter (· > 3) {1,...,5}).
> Then x = a + 1 for some a ∈ {1,...,5} with a > 3.
> Since a > 3, we have a + 1 > 4 and a + 1 ∈ {1,...,6}.
> Therefore x ∈ filter (· > 4) {1,...,6}. □\"

The Lean proof follows exactly this structure.

## What you learned in this world

- **`Finset.filter`** -- selecting elements by a predicate (L01)
- **`Finset.mem_filter`** -- filter membership as conjunction (L01-L02)
- **`Finset.image`** -- applying a function to a finset (L03)
- **`Finset.mem_image`** -- image membership as existential (L03-L04)
- **`Finset.map`** -- image for injective functions (L05)
- **Composing filter and image** -- outside-in reasoning (L06)
- **`Finset.card_image_le`** -- image can shrink cardinality (L07)
- **Integration** -- chaining all tools in a single proof (L08)

## What comes next

In the next world, you will explore a concrete finset {1, 2, 3, 4, 5}
using all the operations you have learned, building intuition before
moving to cardinality.
"

DisabledTactic trivial decide native_decide aesop simp_all
