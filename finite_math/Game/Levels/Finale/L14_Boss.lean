import Game.Metadata

World "Finale"
Level 14

Title "Boss: Finite Injective Functions Are Surjective"

Introduction "
# Boss: The Crown Jewel of Finite Combinatorics

An injective function from a finite type to **itself** must
be surjective. This is one of the most important results in
finite mathematics — it says that for finite sets, 'no
collisions' automatically implies 'everything is hit.'

In CountingTechniques Level 7, you received
`Finite.surjective_of_injective` as a free theorem. Now prove
it yourself using the tools from earlier worlds.

**The proof plan**:
1. Show the image of `f` on `Finset.univ` has cardinality $n$
   (by injectivity: `card_image_of_injective`)
2. The image is a subset of `Finset.univ` (by `subset_univ`)
3. A subset with the same cardinality as the whole set IS the
   whole set (`eq_of_subset_of_card_le` — from Cardinality L24)
4. So every element is in the image
5. Extract the preimage witness
"

/-- An injective endofunction on Fin n is surjective. -/
Statement (n : ℕ) (f : Fin n → Fin n) (hf : Function.Injective f) :
    Function.Surjective f := by
  -- Step 1: Introduce the target element
  Hint "The goal `Function.Surjective f` means `forall y, exists x, f x = y`.
  Start by introducing `y`."
  Hint (hidden := true) "Try `intro y`."
  intro y
  -- Step 2: Compute |image f univ| = n
  Hint "Since `f` is injective, the image of `Finset.univ` under `f`
  has the same cardinality as `Finset.univ`."
  Hint (hidden := true) "Try:
  `have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hf`
  `rw [Finset.card_univ, Fintype.card_fin] at himg`"
  have himg := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hf
  rw [Finset.card_univ, Fintype.card_fin] at himg
  -- Step 3: image ⊆ univ
  Hint "The image sits inside `Finset.univ`."
  Hint (hidden := true) "Try
  `have hsub := Finset.subset_univ (Finset.univ.image f)`."
  have hsub := Finset.subset_univ (Finset.univ.image f)
  -- Step 4: |univ| ≤ |image f univ| (both equal n)
  Hint "Both `univ` and `image f univ` have `n` elements. Prove
  the cardinality bound `|univ| <= |image f univ|`."
  Hint (hidden := true) "Try:
  `have hle : (Finset.univ : Finset (Fin n)).card <= (Finset.univ.image f).card := by`
  `  rw [Finset.card_univ, Fintype.card_fin, himg]`"
  have hle : (Finset.univ : Finset (Fin n)).card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_univ, Fintype.card_fin, himg]
  -- Step 5: image = univ (cardinality sandwich)
  Hint "The **cardinality sandwich**: subset + same cardinality =
  equality. Apply `eq_of_subset_of_card_le`."
  Hint (hidden := true) "Try `have heq := Finset.eq_of_subset_of_card_le hsub hle`."
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  -- Step 6: y ∈ image f
  Hint "Since `image f univ = univ` and `y in univ`, we get `y in image f`."
  Hint (hidden := true) "Try:
  `have hymem : y in Finset.univ.image f := by rw [heq]; exact Finset.mem_univ y`"
  have hymem : y ∈ Finset.univ.image f := by
    rw [heq]
    exact Finset.mem_univ y
  -- Step 7: Extract witness
  Hint "Rewrite using `Finset.mem_image` to expose the existential,
  then extract the witness."
  Hint (hidden := true) "Try:
  `rw [Finset.mem_image] at hymem`
  `obtain ⟨x, _, hfx⟩ := hymem`
  `exact ⟨x, hfx⟩`"
  rw [Finset.mem_image] at hymem
  obtain ⟨x, _, hfx⟩ := hymem
  exact ⟨x, hfx⟩

Conclusion "
**The proof chain**:

| Step | Tool | Result |
|------|------|--------|
| 1 | `intro y` | Fix an arbitrary target |
| 2 | `card_image_of_injective` | $|f(\\text{univ})| = n$ |
| 3 | `subset_univ` | $f(\\text{univ}) \\subseteq \\text{univ}$ |
| 4-5 | cardinality sandwich | $f(\\text{univ}) = \\text{univ}$ |
| 6 | `mem_univ` | $y \\in f(\\text{univ})$ |
| 7 | `mem_image` + `obtain` | extract preimage $x$ |

This proof integrates techniques from across the course:
- **Phase 2** (Finset): `mem_image`, `subset_univ`, image operations
- **Phase 3** (Cardinality): `card_image_of_injective`,
  `eq_of_subset_of_card_le`, `card_univ`, `card_fin`
- **Phase 7** (Counting): The injection/surjection relationship

The key insight is the **cardinality sandwich** (Steps 4-5): a
subset of a finite set with the same cardinality must be the
entire set. This is the forward counterpart of the pigeonhole
principle — instead of deriving a contradiction from 'too many
items in too few bins,' you derive an equality from 'exactly the
right number of items in the right number of bins.'

**Why finiteness is essential**: This theorem is FALSE for
infinite types. The function $f(n) = n + 1$ on $\\mathbb{N}$ is
injective but not surjective ($0$ has no preimage). In the next
level, you will prove this formally — making the role of
finiteness visceral, not just theoretical.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Disable all shortcuts that give injective → surjective for free
DisabledTheorem Finite.surjective_of_injective Fintype.surjective_of_injective Fintype.injective_iff_surjective Fintype.injective_iff_bijective Fintype.surjective_iff_bijective Finset.eq_univ_of_card Finset.map_eq_of_subset Finset.image_univ_of_surjective Equiv.ofBijective Fintype.card_of_bijective Fintype.card_congr Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
