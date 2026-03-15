import GameServer.Commands
import Mathlib

World "FinsetExploration"
Level 7

Title "Boss: The full inventory"

Introduction
"
# Boss: Integrating everything on {1, 2, 3, 4, 5}

You have now built, filtered, mapped, and combined finsets. Time to
integrate these skills in a single proof.

## Your task

Prove a four-part conjunction about our running example:

1. **Filter cardinality**: The even elements of {1, 2, 3, 4, 5}
   form a finset of size 2.

2. **Image cardinality**: The image of {1, 2, 3, 4, 5} under
   squaring has 5 elements (no collisions since squaring is injective
   on these values).

3. **Powerset cardinality**: The powerset of {1, 2, 3} has
   2³ = 8 elements.

4. **Product cardinality**: The cardinality of {1, 2} ×ˢ {3, 4}
   equals |{1, 2}| × |{3, 4}|.

Each part uses a technique from an earlier level of this world:
- L03: `ext` + `simp` + `omega` (filter)
- L04: `ext` + `simp` + case analysis (image)
- L05: `Finset.card_powerset` (powerset)
- L06: `Finset.card_product` (product)

There is no new material. This is pure integration.
"

/-- Four cardinality facts about finset operations on {1, 2, 3, 4, 5}. -/
Statement :
    (Finset.filter (fun x => x % 2 = 0) ({1, 2, 3, 4, 5} : Finset Nat)).card = 2 ∧
    (Finset.image (· ^ 2) ({1, 2, 3, 4, 5} : Finset Nat)).card = 5 ∧
    ({1, 2, 3} : Finset Nat).powerset.card = 8 ∧
    (({1, 2} : Finset Nat) ×ˢ ({3, 4} : Finset Nat)).card =
      ({1, 2} : Finset Nat).card * ({3, 4} : Finset Nat).card := by
  Hint "This is a four-part conjunction. Use `refine ⟨?_, ?_, ?_, ?_⟩`
  to split into four goals at once, or use `constructor` repeatedly."
  Hint (hidden := true) "Use `refine ⟨?_, ?_, ?_, ?_⟩`."
  refine ⟨?_, ?_, ?_, ?_⟩
  · Hint "**Part 1**: Show the cardinality of the even-filtered finset
    is 2. One approach: first show the filter equals a known finset,
    then compute its cardinality."
    Hint (hidden := true) "Use a `have` to show the filter equals the
    finset of evens, then `rw` and compute. Or use
    `simp [Finset.filter_insert, Finset.filter_singleton]`."
    have h : Finset.filter (fun x => x % 2 = 0) ({1, 2, 3, 4, 5} : Finset Nat) = {2, 4} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [h]; rfl
  · Hint "**Part 2**: Show the image under squaring has 5 elements.
    First show the image equals the finset of squares, then compute."
    Hint (hidden := true) "Use a `have` to identify the image, then
    `rw` and compute the cardinality."
    have h : Finset.image (· ^ 2) ({1, 2, 3, 4, 5} : Finset Nat) = {1, 4, 9, 16, 25} := by
      ext x
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨a, ha, rfl⟩; rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp
      · rintro (rfl | rfl | rfl | rfl | rfl)
        · exact ⟨1, by simp, by ring⟩
        · exact ⟨2, by simp, by ring⟩
        · exact ⟨3, by simp, by ring⟩
        · exact ⟨4, by simp, by ring⟩
        · exact ⟨5, by simp, by ring⟩
    rw [h]; rfl
  · Hint "**Part 3**: Show the powerset has 8 elements.
    Use `Finset.card_powerset` to reduce to a power-of-2 computation."
    Hint (hidden := true) "Use `rw [Finset.card_powerset]` then `rfl`."
    rw [Finset.card_powerset]; rfl
  · Hint "**Part 4**: The product cardinality formula. Use
    `Finset.card_product` directly."
    Hint (hidden := true) "Use `rw [Finset.card_product]`."
    rw [Finset.card_product]

Conclusion
"
Congratulations on completing the Finset Exploration world!

You proved four cardinality facts, each using a different technique:

1. **Filter cardinality** (L03): `ext` + membership reasoning to identify
   the filtered finset, then compute its size.

2. **Image cardinality** (L04): Identify the image under squaring, then
   compute its size. All 5 squares are distinct.

3. **Powerset cardinality** (L05): `Finset.card_powerset` reduces to
   `2 ^ 3 = 8`.

4. **Product cardinality** (L06): `Finset.card_product` gives the
   multiplication principle directly.

## Transfer moment

In ordinary mathematics, these are the basic counting principles:

- **Filtering**: Count the elements that satisfy a property. Of the
  5 numbers 1--5, exactly 2 are even.

- **Image under injection**: An injective function preserves the count.
  The 5 distinct squares are all different, so there are 5 of them.

- **Powerset**: A set of n elements has 2^n subsets. Each element is
  independently either included or excluded: 2 choices per element.

- **Cartesian product**: |A x B| = |A| * |B|. Each pair consists of
  one choice from A and one from B.

These four principles -- filtering, injective image, powerset counting,
and the multiplication principle -- are the cornerstones of elementary
combinatorics.

## What you learned in this world

| Concept | Level | Proof move |
|---------|-------|------------|
| Three constructions | L01 | `rfl`, `ext` + `simp` + `omega` |
| Membership/non-membership | L02 | `simp [mem_insert, mem_singleton]` |
| Concrete filter | L03 | `ext` + `mem_filter` + `omega` |
| Concrete image | L04 | `ext` + `mem_image` + witness |
| Powerset preview | L05 | `card_powerset` |
| Product preview | L06 | `mem_product`, `card_product` |
| Integration | L07 | All of the above |

## What comes next

You are now fluent with concrete finset operations. The next world
introduces **cardinality** as a systematic topic: `Finset.card`,
`card_empty`, `card_singleton`, `card_insert_of_not_mem`, the
inclusion-exclusion principle, and `Finset.range`.
"

DisabledTactic trivial decide native_decide aesop simp_all
