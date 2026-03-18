import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 14

Title "Boss: Antisymmetry from Scratch"

Introduction
"
# Boss Level

You have learned:
- `show` and `change` to see through set membership notation
- `intro` to open subset proofs
- `specialize` and direct application to use subset hypotheses
- `constructor` to split iff statements
- `.mp` and `.mpr` to use iff hypotheses
- `ext` to reduce set equality to membership equivalence
- `Set.Subset.antisymm` as a theorem

Now prove the **antisymmetry theorem from scratch**: if `A ⊆ B` and
`B ⊆ A`, then `A = B`. But this time, you may *not* use
`Set.Subset.antisymm` — you must build the proof yourself using `ext`.

The proof requires you to:
1. Apply `ext` to reduce equality to a pointwise iff.
2. Split the iff with `constructor`.
3. In each direction, use the appropriate subset hypothesis.

This integrates the three main skills of the world: extensionality,
iff splitting, and subset application.
"

TheoremTab "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num
DisabledTheorem Set.Subset.antisymm le_antisymm Subset.antisymm Set.eq_of_subset_of_subset LE.le.antisymm eq_of_subset_of_subset

Statement (A B : Set ℕ) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B := by
  Hint "This is the boss. You need to prove `A = B` from `h1 : A ⊆ B` and
  `h2 : B ⊆ A`, without using `Set.Subset.antisymm`.

  Start with `ext x` to reduce the equality to a pointwise iff."
  ext x
  Hint "The goal is now `x ∈ A ↔ x ∈ B`. Use `constructor` to split
  it into the forward and backward implications."
  constructor
  · Hint "Forward: assume `x ∈ A`, prove `x ∈ B`. Use the subset
    hypothesis `h1`. Try `intro hx` then `exact h1 hx`."
    intro hx
    exact h1 hx
  · Hint "Backward: assume `x ∈ B`, prove `x ∈ A`. Use `h2`.
    Try `intro hx` then `exact h2 hx`."
    intro hx
    exact h2 hx

Conclusion
"
# Congratulations!

You proved the antisymmetry of subset from first principles.

Let us step back and see what happened in ordinary mathematics:

*To show A = B, we show they have the same elements. Take any x.
If x ∈ A, then x ∈ B because A ⊆ B. If x ∈ B, then x ∈ A because
B ⊆ A. So x ∈ A ↔ x ∈ B, and since x was arbitrary, A = B.*

Your Lean proof was a direct formalization of this argument:
- `ext x` — 'take any x'
- `constructor` — 'we show both directions'
- `intro hx; exact h1 hx` — 'if x ∈ A then x ∈ B by h1'
- `intro hx; exact h2 hx` — 'if x ∈ B then x ∈ A by h2'

This **ext → constructor → chase** pattern is the most important proof
shape in this course. You will use it again and again as we move to
set operations, functions, and beyond.

**World complete!** You now know how to:
- Prove set membership using `show` and `change`
- Prove subset relationships using `intro`
- Use subset hypotheses with `specialize` or direct application
- Prove set equality using `ext` (extensionality)
- Prove set equality using `Set.Subset.antisymm` (double inclusion)
- Work with `∅` and `Set.univ`
- Split and use `↔` statements (with `constructor`, `.mp`, `.mpr`)

Next world: **Set Operations** — where you will learn to prove
identities involving union, intersection, difference, and complement.
"
