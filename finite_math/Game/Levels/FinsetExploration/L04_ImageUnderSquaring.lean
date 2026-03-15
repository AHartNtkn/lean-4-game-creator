import GameServer.Commands
import Mathlib

World "FinsetExploration"
Level 4

Title "Image under squaring"

Introduction
"
# Squaring every element of {1, 2, 3, 4, 5}

Recall `Finset.image f s` applies a function `f` to every element of `s`
and collects the results (removing duplicates). The key lemma:

```
Finset.mem_image : b ∈ Finset.image f s ↔ ∃ a ∈ s, f a = b
```

## Your task

Prove that the image of {1, 2, 3, 4, 5} under the squaring function
`x ↦ x ^ 2` is {1, 4, 9, 16, 25}.

Since `x ↦ x ^ 2` is injective on {1, 2, 3, 4, 5}, no duplicates are
removed: the image has the same number of elements as the source.

**Strategy**: Use `ext x` to reduce to membership, then `simp` with
the image and insert membership lemmas, and handle each direction.
"

/-- The image of {1,2,3,4,5} under squaring is {1, 4, 9, 16, 25}. -/
Statement : Finset.image (· ^ 2) ({1, 2, 3, 4, 5} : Finset Nat) =
    ({1, 4, 9, 16, 25} : Finset Nat) := by
  Hint "Use `ext x` to reduce the equality to a membership equivalence."
  Hint (hidden := true) "Use `ext x`."
  ext x
  Hint "Now simplify with the membership lemmas for image, insert, and
  singleton."
  Hint (hidden := true) "Use `simp only [Finset.mem_image, Finset.mem_insert,
  Finset.mem_singleton]` and then handle what remains."
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  Hint "The goal now asks: does there exist an `a` that equals one of
  1, 2, 3, 4, 5, with `a ^ 2 = x`? This is equivalent to `x` being
  one of 1, 4, 9, 16, 25.

  Use `constructor` to prove the biconditional."
  Hint (hidden := true) "Use `constructor` then handle each direction.
  For the forward direction, use `rintro ⟨a, ha, rfl⟩` to extract the
  witness and substitute."
  constructor
  · Hint "Extract the witness: `rintro ⟨a, ha, rfl⟩` gives an element
    `a` from the source with `a ^ 2 = x` (substituted via `rfl`)."
    Hint (hidden := true) "Use `rintro ⟨a, ha, rfl⟩`."
    rintro ⟨a, ha, rfl⟩
    Hint "Now the goal is about `a ^ 2` and you know `a` equals one of
    1, 2, 3, 4, or 5 from `ha`. Case-split on `ha` and compute."
    Hint (hidden := true) "Use `rcases ha with rfl | rfl | rfl | rfl | rfl`
    then close each with `simp`."
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp
  · Hint "For the reverse direction, given `x` is one of 1, 4, 9, 16, 25,
    provide the square root as a witness."
    Hint (hidden := true) "Use `rintro (rfl | rfl | rfl | rfl | rfl)` then
    provide the witness with `exact ⟨_, by simp, by ring⟩`."
    rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, by simp, by ring⟩
    · exact ⟨2, by simp, by ring⟩
    · exact ⟨3, by simp, by ring⟩
    · exact ⟨4, by simp, by ring⟩
    · exact ⟨5, by simp, by ring⟩

Conclusion
"
You proved that squaring {1, 2, 3, 4, 5} gives {1, 4, 9, 16, 25}.

The proof had two directions:
- **Forward**: Given a witness `a ∈ {1,...,5}` with `a ^ 2 = x`, case-split
  on which element `a` is and compute the square.
- **Backward**: Given `x ∈ {1, 4, 9, 16, 25}`, provide the square root
  as a witness.

## Squaring is injective here

Notice that all five squares are distinct: 1, 4, 9, 16, 25. This is
because `x ↦ x ^ 2` is injective on positive natural numbers. If we had
included negative numbers (in `Int`), we would see collisions:
`(-2)^2 = 2^2 = 4`.

## Contrast with filter

| Operation | Membership proof shape |
|-----------|----------------------|
| `filter p s` | Conjunction: `a ∈ s ∧ p a` |
| `image f s` | Existential: `∃ a ∈ s, f a = b` |

Filtering checks a property. Image requires a **witness** -- an element
that maps to the target.

**In plain language**: \"Squaring each element of {1, 2, 3, 4, 5} gives
{1, 4, 9, 16, 25}. Each output has a unique preimage in the original set.\"
"

/-- `rintro` is a pattern-matching variant of `intro`. It can destructure
hypotheses as they are introduced.

For example, `rintro ⟨a, ha, rfl⟩` introduces an existential and
simultaneously names the witness `a`, the membership proof `ha`, and
substitutes the equation into the goal using `rfl`.

This is especially useful for unpacking `mem_image` hypotheses:
if `hx : ∃ a ∈ s, f a = x`, then `rintro ⟨a, ha, rfl⟩` replaces `x`
with `f a` throughout. -/
TacticDoc rintro

/-- `ring` closes goals that are equalities in commutative (semi)rings.
It handles addition, multiplication, and powers over types like `Nat`,
`Int`, `Rat`, and `Real`.

For example, `ring` can prove `(a + b)^2 = a^2 + 2*a*b + b^2`. -/
TacticDoc ring

NewTactic rintro ring
DisabledTactic trivial decide native_decide aesop simp_all
