import Game.Metadata

World "Cardinality"
Level 25

Title "Surjective Implies Image = Univ"

Introduction "
# The Converse Direction

Level 24 proved: if `f : Fin 5 -> Fin 5` is **injective**, then
`univ.image f = univ` (i.e., f is surjective).

Now prove the converse: if `f` is **surjective**, then
`univ.image f = univ`.

The proof uses the same key lemma — `eq_of_subset_of_card_le` — but
the cardinality bound comes from a different source:

- **Level 23** (injective direction): the image has exactly `n`
  elements because injectivity preserves cardinality.
- **This level** (surjective direction): `univ` is a subset of the
  image (because surjectivity means every element is hit), so
  `card_le_card` gives `univ.card <= (univ.image f).card`.

The two directions together give the complete characterization:
for endofunctions on finite types, `image f univ = univ` iff `f`
is injective iff `f` is surjective.

**Your task**: Prove that if `f : Fin 5 -> Fin 5` is surjective,
then `univ.image f = univ`.
"

/-- A surjective function on Fin 5 maps univ to univ. -/
Statement (f : Fin 5 → Fin 5) (hsurj : Function.Surjective f) :
    Finset.univ.image f = Finset.univ := by
  Hint "Use `eq_of_subset_of_card_le` — the same tool as Level 24.
  `apply Finset.eq_of_subset_of_card_le` splits the goal into:
  1. The image is a subset of univ (always true)
  2. `univ.card <= (univ.image f).card` (from surjectivity)"
  Hint (hidden := true) "`apply Finset.eq_of_subset_of_card_le`"
  apply Finset.eq_of_subset_of_card_le
  -- Goal 1: univ.image f ⊆ univ
  · Hint "Everything is a subset of univ."
    Hint (hidden := true) "`exact Finset.subset_univ _`"
    exact Finset.subset_univ _
  -- Goal 2: univ.card ≤ (univ.image f).card
  · Hint "You need `univ.card <= (univ.image f).card`. The idea:
    surjectivity means every element of `univ` is in the image, so
    `univ ⊆ univ.image f`. Then `card_le_card` converts the subset
    to a cardinality bound."
    Hint (hidden := true) "`apply Finset.card_le_card`"
    apply Finset.card_le_card
    Hint "Now prove `univ ⊆ univ.image f`: for every `y : Fin 5`,
    show `y ∈ univ.image f`. Surjectivity gives a witness."
    rw [Finset.subset_iff]
    intro y _
    Hint "The goal is `y ∈ Finset.univ.image f`. Use backward image
    membership: provide an `x` with `x ∈ univ` and `f x = y`.
    Surjectivity gives you such an `x`."
    Hint (hidden := true) "`rw [Finset.mem_image]`
    `obtain ⟨x, hx⟩ := hsurj y`
    `exact ⟨x, Finset.mem_univ x, hx⟩`"
    rw [Finset.mem_image]
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, Finset.mem_univ x, hx⟩

Conclusion "
You've proved both directions of the characterization:

| Direction | Proved in | Key cardinality tool |
|---|---|---|
| Injective -> image = univ | Level 24 | `card_image_of_injective` |
| Surjective -> image = univ | This level | `card_le_card` + surjectivity |

Together: for `f : Fin n -> Fin n`:
- **Injective iff surjective iff bijective**

This is one of the deepest consequences of finiteness. For infinite
types, these three properties are genuinely independent:
- The function $n \\mapsto 2n$ on $\\mathbb{N}$ is **injective but not surjective**
  (1 is not in the range)
- The function $n \\mapsto \\lfloor n/2 \\rfloor$ on $\\mathbb{N}$ is **surjective but not
  injective** (both 0 and 1 map to 0)

For finite types, the counting argument collapses all three into one:
if $f$ hits $n$ distinct outputs (injective), those $n$ outputs must
be everything (surjective), and vice versa. Finiteness is what makes
'no room left over' a valid deduction.

The proof strategy was different from Level 24:
- Level 24 used `card_image_of_injective` to show the image is big
  enough (has `n` elements)
- This level used surjectivity to show `univ ⊆ image`, then
  `card_le_card` for the cardinality bound

Both converge on `eq_of_subset_of_card_le` — the workhorse lemma
that turns 'subset + large enough' into equality.

**The bidirectional result via card_image_iff**: `Finset.card_image_iff`
says `(s.image f).card = s.card ↔ Set.InjOn f s`. Since `image = univ`
implies `card (image) = card (univ)`, surjectivity gives `InjOn f univ`
— which is injectivity. The counting bridge makes both directions
trivial once you have `image = univ`.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Fintype.surjective_of_injective Fintype.injective_iff_surjective Fintype.injective_iff_bijective Fintype.surjective_iff_bijective Finset.map_eq_of_subset Finset.eq_univ_of_card Finset.image_univ_of_surjective
