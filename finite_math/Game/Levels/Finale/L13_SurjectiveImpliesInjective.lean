import Game.Metadata

World "Finale"
Level 13

Title "Surjective Implies Injective"

Introduction "
# The Other Direction

The boss will prove: injective endofunctions on `Fin n` are
surjective. But the converse is equally true and equally
important: **surjective** endofunctions are **injective**.

Together they give the full equivalence: for finite types,
injective iff surjective iff bijective.

**The proof plan**:
1. Show `image f univ = univ` (from surjectivity — every
   element has a preimage, so every element is in the image)
2. Derive `|image f univ| = |univ|` (from step 1)
3. Use `card_image_iff`: `|image| = |source|` implies
   `f` is injective on the source
4. Convert the set-level injectivity to function-level
   injectivity
"

/-- A surjective endofunction on Fin n is injective. -/
Statement (n : ℕ) (f : Fin n → Fin n) (hf : Function.Surjective f) :
    Function.Injective f := by
  -- Step 1: image f univ = univ
  Hint "First show that the image of `f` covers everything.
  Since `f` is surjective, every element of `Fin n` is in
  `Finset.univ.image f`. Use the **cardinality sandwich**
  (`eq_of_subset_of_card_le`) to derive set equality."
  Hint (hidden := true) "Try:
  `have heq : Finset.univ.image f = (Finset.univ : Finset (Fin n)) := by`
  `  apply Finset.eq_of_subset_of_card_le`
  `  · exact Finset.subset_univ _`
  `  · apply Finset.card_le_card`
  `    intro y _`
  `    rw [Finset.mem_image]`
  `    obtain ⟨x, hx⟩ := hf y`
  `    exact ⟨x, Finset.mem_univ x, hx⟩`"
  have heq : Finset.univ.image f = (Finset.univ : Finset (Fin n)) := by
    Hint "Apply the cardinality sandwich: show the image is a subset of
    `univ` with at least as many elements."
    Hint (hidden := true) "Try `apply Finset.eq_of_subset_of_card_le`."
    apply Finset.eq_of_subset_of_card_le
    · Hint "The image of any function on `univ` is a subset of `univ`."
      Hint (hidden := true) "Try `exact Finset.subset_univ _`."
      exact Finset.subset_univ _
    · Hint "Show `|univ| <= |image f univ|`. Since `f` is surjective,
      every element has a preimage in the image. Use `card_le_card`."
      Hint (hidden := true) "Try `apply Finset.card_le_card`."
      apply Finset.card_le_card
      Hint "For each `y` in `univ`, show `y` is in `image f univ`.
      Introduce `y`, rewrite with `mem_image`, then use surjectivity
      to find a preimage."
      Hint (hidden := true) "Try:
      `intro y _`
      `rw [Finset.mem_image]`
      `obtain ⟨x, hx⟩ := hf y`
      `exact ⟨x, Finset.mem_univ x, hx⟩`"
      intro y _
      rw [Finset.mem_image]
      obtain ⟨x, hx⟩ := hf y
      exact ⟨x, Finset.mem_univ x, hx⟩
  -- Step 2: |image| = |univ|
  Hint "Derive the cardinality equality from the set equality."
  Hint (hidden := true) "Try:
  `have hcard : (Finset.univ.image f).card = (Finset.univ : Finset (Fin n)).card := by rw [heq]`"
  have hcard : (Finset.univ.image f).card = (Finset.univ : Finset (Fin n)).card := by
    rw [heq]
  -- Step 3: card_image_iff → InjOn
  Hint "Use `Finset.card_image_iff` to convert the cardinality
  equality into injectivity on the source set."
  Hint (hidden := true) "Try:
  `have hinj_on := Finset.card_image_iff.mp hcard`"
  have hinj_on := Finset.card_image_iff.mp hcard
  -- Step 4: InjOn → Injective
  Hint "`hinj_on` says `f` is injective on `Finset.univ` (as a set).
  Since every element of `Fin n` is in `Finset.univ`, this gives
  full injectivity."
  Hint (hidden := true) "Try:
  `intro a b hab`
  `exact hinj_on (Finset.mem_univ a) (Finset.mem_univ b) hab`"
  intro a b hab
  exact hinj_on (Finset.mem_univ a) (Finset.mem_univ b) hab

Conclusion "
**Surjective implies injective** for finite endofunctions.

| Step | Tool | Result |
|------|------|--------|
| 1 | `eq_of_subset_of_card_le` + surjectivity | `image f univ = univ` |
| 2 | `congr_arg card` | `|image| = |univ|` |
| 3 | `card_image_iff` | `f` is injective on `univ` |
| 4 | `mem_univ` | full injectivity |

**The full equivalence**: For `f : Fin n -> Fin n`:
- **Injective -> surjective** (the boss, Level 14)
- **Surjective -> injective** (this level, Level 13)

So injective, surjective, and bijective are all equivalent
for endofunctions on finite types. This is one of the most
important consequences of finiteness.

**Contrast with the boss**: The boss (injective -> surjective)
uses `card_image_of_injective` to compute |image| = n, then
`eq_of_subset_of_card_le` to get image = univ, then extracts
a preimage. This level uses surjectivity to show univ is
contained in the image, then `eq_of_subset_of_card_le` to
get image = univ, then `card_image_iff` to extract
injectivity.

Both converge on the **cardinality sandwich**
(`eq_of_subset_of_card_le`) — the same lemma, applied with
cardinality information flowing in opposite directions.
"

TheoremTab "Fintype"

/-- `Finite.injective_of_surjective` proves that a surjective function
from a finite type to itself is injective. Disabled so you prove it
yourself using image cardinality reasoning. -/
TheoremDoc Finite.injective_of_surjective as "Finite.injective_of_surjective" in "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Disable all shortcuts
DisabledTheorem Finite.surjective_of_injective Fintype.surjective_of_injective Fintype.injective_iff_surjective Fintype.injective_iff_bijective Fintype.surjective_iff_bijective Finset.eq_univ_of_card Finset.map_eq_of_subset Finset.image_univ_of_surjective Equiv.ofBijective Fintype.card_of_bijective Fintype.card_congr Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt Finite.injective_of_surjective
