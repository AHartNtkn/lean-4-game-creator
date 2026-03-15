import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 13

Title "The reduce-then-compute pattern"

Introduction
"
# Naming a proof strategy

Throughout this world, you have been using a recurring two-step proof
pattern without naming it. It is time to give it a name.

## The reduce-then-compute pattern

Many proofs in this world follow the same shape:

1. **Reduce**: Use a structural lemma (`rw [bridge_lemma]`) to convert
   a derived-type question (about multisets, finsets) into a base-type
   question (about lists, natural numbers).
2. **Compute**: Close the simplified goal with `decide`, `rfl`, or `exact`.

Examples from this world:
- L02: `rw [Multiset.mem_coe]; decide` (membership)
- L03: `rw [Multiset.coe_eq_coe]; decide` (equality)
- L05: `rw [Multiset.card_map]; rfl` (cardinality)
- L07: `rw [Multiset.count_cons_self]; decide` (counting)
- L12: `rw [Multiset.coe_nodup]; decide` (nodup)

The bridge lemma does the conceptual work (it reveals the structure),
and the computation tactic does the mechanical work.

## Why name this pattern?

In later worlds, you will encounter similar patterns with finset lemmas:
reduce a finset question to a multiset or list question using
`Finset.mem_insert`, `Finset.ext`, etc., then compute. Recognizing the
reduce-then-compute shape helps you plan proofs: \"What bridge lemma
do I need to make this concrete?\"

## Your task

Practice the pattern one more time: prove that `Multiset.map (· * 2)`
applied to `↑[1, 2, 3]` gives a multiset equal to `↑[2, 4, 6]`.

**Strategy**:
1. `rw [Multiset.coe_eq_coe]` to reduce multiset equality to list permutation
2. But wait -- `Multiset.map` on a coerced list might not directly simplify
   to a coercion. Instead, use `rw [Multiset.map_coe]` first to push the
   map inside the coercion, giving `↑(List.map (· * 2) [1, 2, 3]) = ↑[2, 4, 6]`.
3. Then `rw [Multiset.coe_eq_coe]` reduces to a permutation.
4. `decide` finishes.
"

/-- Mapping (· * 2) over `↑[1, 2, 3]` gives the multiset `↑[2, 4, 6]`. -/
Statement : Multiset.map (· * 2) (↑([1, 2, 3] : List Nat) : Multiset Nat) =
    ↑([2, 4, 6] : List Nat) := by
  Hint "The goal has `Multiset.map` applied to a coerced list on the left.
  The **reduce** step: use `rw [Multiset.map_coe]` to push the map inside
  the coercion, converting `Multiset.map f ↑l` into `↑(List.map f l)`."
  Hint (hidden := true) "Try `rw [Multiset.map_coe]`. This converts
  `Multiset.map (· * 2) ↑[1, 2, 3]` to `↑(List.map (· * 2) [1, 2, 3])`."
  rw [Multiset.map_coe]
  Hint "Now both sides are coerced lists. Use `rw [Multiset.coe_eq_coe]` to
  reduce to a permutation check."
  rw [Multiset.coe_eq_coe]
  Hint "The **compute** step: verify the permutation with `decide`."
  decide

Conclusion
"
You executed a three-step reduce-then-compute proof:

1. `rw [Multiset.map_coe]` -- pushed the map inside the coercion
2. `rw [Multiset.coe_eq_coe]` -- reduced multiset equality to permutation
3. `decide` -- verified the permutation

Each `rw` step was a **reduction** (converting a multiset question to a
simpler form), and `decide` was the **computation**.

**The reduce-then-compute recipe**:
1. Look at the goal: what derived type is involved? (Multiset? Finset?)
2. Find the bridge lemma that converts to a base type (List, Nat, Prop)
3. `rw [bridge_lemma]`
4. Repeat if needed (some goals need multiple reductions)
5. Close with `decide`, `rfl`, or `exact`

This is one of the most transferable proof strategies from this world.
In later courses, you will apply it to rings (`rw [ring_lemma]; ring`),
groups (`rw [group_lemma]; group`), and other algebraic structures.

**In plain language**: \"To answer a question about a derived structure,
translate it back to the underlying structure, then compute there.\"
"

/-- `Multiset.map_coe` states that `Multiset.map f ↑l = ↑(List.map f l)`.
Mapping a function over a coerced list is the same as mapping the function
over the list and then coercing. This lets you push `Multiset.map` inside
the coercion `↑`. -/
TheoremDoc Multiset.map_coe as "Multiset.map_coe" in "Multiset"

NewTheorem Multiset.map_coe
DisabledTactic trivial decide native_decide simp aesop simp_all
