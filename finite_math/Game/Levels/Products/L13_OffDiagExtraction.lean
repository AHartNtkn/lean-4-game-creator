import Game.Metadata

World "Products"
Level 13

Title "Off-Diagonal Extraction"

Introduction "
# Extracting from the Off-Diagonal

In the previous level you built off-diagonal membership from
component memberships and a disequality. Now let's go the
other direction: **extract** information from an off-diagonal
hypothesis.

If `(a, b) ∈ s.offDiag`, you can extract three facts:
- `a ∈ s`
- `b ∈ s`
- `a ≠ b`

This extraction is more interesting than product extraction
(which gives only two facts) because you also get the
**distinctness proof** `a ≠ b`.

**Your task**: Given `(a, b) ∈ s.offDiag`, prove `(b, a) ∈ s.offDiag`.

This shows that the off-diagonal is **symmetric**: if `(a, b)` is
an ordered pair of distinct elements, then so is `(b, a)`.
You'll need to flip the disequality using `Ne.symm`.
"

/-- The off-diagonal is symmetric: swap the pair. -/
Statement (s : Finset ℕ) (a b : ℕ) (h : (a, b) ∈ s.offDiag) :
    (b, a) ∈ s.offDiag := by
  Hint "First extract the components from `h`. Rewrite
  `Finset.mem_offDiag` at `h` to expose the conjunction."
  Hint (hidden := true) "Try `rw [Finset.mem_offDiag] at h`."
  rw [Finset.mem_offDiag] at h
  Hint "Now `h : a ∈ s ∧ b ∈ s ∧ a ≠ b`. Rewrite the goal
  with `Finset.mem_offDiag` too."
  Hint (hidden := true) "Try `rw [Finset.mem_offDiag]`."
  rw [Finset.mem_offDiag]
  Hint "You need `b ∈ s ∧ a ∈ s ∧ b ≠ a`. The first two come
  from `h`, and for `b ≠ a` you can use `Ne.symm` to flip
  the `a ≠ b` from `h`."
  Hint (hidden := true) "Try `exact ⟨h.2.1, h.1, Ne.symm h.2.2⟩`.

  Here `h.1 : a ∈ s`, `h.2.1 : b ∈ s`, and
  `Ne.symm h.2.2 : b ≠ a` (flipped from `a ≠ b`)."
  exact ⟨h.2.1, h.1, Ne.symm h.2.2⟩

Conclusion "
Extraction from `s.offDiag` gives three pieces:
1. First component membership: `h.1`
2. Second component membership: `h.2.1`
3. Distinctness: `h.2.2`

The symmetry proof is another instance of the **membership
round-trip** from Level 4: extract the components, transform
them (swap the membership order and flip the disequality with
`Ne.symm`), then rebuild the off-diagonal membership.

The pattern is the same — only the membership characterization
changed from `mem_product` to `mem_offDiag`.

**A consequence of symmetry**: Since every off-diagonal pair
`(a, b)` has a companion `(b, a)` also in `s.offDiag`, the
off-diagonal elements come in pairs. This means
`s.offDiag.card` is always even. Keep this in mind — when
you see the formula $|s.\\text{offDiag}| = 2 \\binom{n}{2}$ in
a later level, the factor of 2 is exactly this pairing.
"

/-- `Ne.symm` flips a disequality:

`Ne.symm : a ≠ b → b ≠ a`

If you have `h : a ≠ b`, then `Ne.symm h : b ≠ a`.

## Syntax
```
Ne.symm h       -- flip h : a ≠ b to b ≠ a
exact Ne.symm h -- use the flipped disequality
```

## When to use it
When you need `b ≠ a` but have `a ≠ b` — for example, when
swapping the components of an off-diagonal pair.
-/
TheoremDoc Ne.symm as "Ne.symm" in "Logic"

/-- `Finset.offDiag_mono` states that the off-diagonal is monotone:
if `s ⊆ t` then `s.offDiag ⊆ t.offDiag`.

Disabled to force manual extraction and reconstruction of
off-diagonal membership.
-/
TheoremDoc Finset.offDiag_mono as "Finset.offDiag_mono" in "Product"

/-- `Finset.Pairwise.mono` weakens a pairwise relation by a subset:
if a relation holds pairwise on `t` and `s ⊆ t`, it holds on `s`.

Disabled to keep the focus on direct membership reasoning.
-/
TheoremDoc Finset.Pairwise.mono as "Finset.Pairwise.mono" in "Product"

/-- `Finset.offDiag_pairDisjoint` states that `s.offDiag` is
pairwise disjoint for certain relations.

Disabled to keep focus on the main off-diagonal API.
-/
TheoremDoc Finset.offDiag_pairDisjoint as "Finset.offDiag_pairDisjoint" in "Product"

TheoremTab "Product"
NewTheorem Ne.symm

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finset.offDiag_mono Finset.Pairwise.mono Finset.offDiag_pairDisjoint
