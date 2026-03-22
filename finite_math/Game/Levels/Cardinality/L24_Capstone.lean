import Game.Metadata

World "Cardinality"
Level 24

Title "Injective Implies Surjective (Finite Types)"

Introduction "
# The Capstone Theorem

You've assembled all the pieces. Now for the punchline.

For finite types, **injectivity implies surjectivity**. If
`f : Fin n -> Fin n` is injective (different inputs give different
outputs), then `f` is also surjective (every output is hit).

Why? The image `Finset.univ.image f` satisfies:
- It has `n` elements (by `card_image_of_injective`, since `f` is injective)
- It is a subset of `Finset.univ` (by `subset_univ`, since everything
  lives in the universe)

A subset with the same number of elements as the whole must BE the
whole. This is `Finset.eq_of_subset_of_card_le`:

```
Finset.eq_of_subset_of_card_le : s ⊆ t → #t ≤ #s → s = t
```

If a subset is at least as large as its superset, they're equal.

**Your task**: Prove that if `f : Fin 5 -> Fin 5` is injective, then
the image of `univ` under `f` equals `univ` — meaning `f` hits every
element.
"

/-- An injective function on Fin 5 maps univ to univ. -/
Statement (f : Fin 5 → Fin 5) (hinj : Function.Injective f) :
    Finset.univ.image f = Finset.univ := by
  Hint "Step 1: Compute the image size. Use `card_image_of_injective`
  with `hinj`, then simplify with `card_univ` and `card_fin`."
  Hint (hidden := true) "`have h1 := Finset.card_image_of_injective Finset.univ hinj`
  `rw [Finset.card_univ, Fintype.card_fin] at h1`"
  have h1 := Finset.card_image_of_injective Finset.univ hinj
  rw [Finset.card_univ, Fintype.card_fin] at h1
  Hint "Step 2: The image is a subset of univ."
  Hint (hidden := true) "`have h2 := Finset.subset_univ (Finset.univ.image f)`"
  have h2 := Finset.subset_univ (Finset.univ.image f)
  Hint "Step 3: Apply `eq_of_subset_of_card_le`. A subset with at
  least as many elements as its superset must be equal.
  Use `apply Finset.eq_of_subset_of_card_le h2` to reduce to proving
  the cardinality bound."
  Hint (hidden := true) "`apply Finset.eq_of_subset_of_card_le h2`"
  apply Finset.eq_of_subset_of_card_le h2
  Hint "Step 4: The remaining goal is `Finset.univ.card <= (Finset.univ.image f).card`.
  Simplify `univ.card` using `card_univ` and `card_fin`, then use
  `h1` and `omega`."
  Hint (hidden := true) "`rw [Finset.card_univ, Fintype.card_fin]; omega`"
  rw [Finset.card_univ, Fintype.card_fin]
  omega

Conclusion "
This is the single most important theorem in finite mathematics:

> For a function `f : X -> X` on a finite set, **injective implies
> surjective** (and therefore bijective).

The proof uses nothing beyond what you've learned:
1. `card_image_of_injective` — injectivity preserves image size
2. `subset_univ` — the image lives in the universe
3. `eq_of_subset_of_card_le` — a subset as large as the whole IS the whole

For infinite types, this fails spectacularly. The function
`f(n) = n + 1` on the natural numbers is injective (different inputs
give different outputs) but NOT surjective (nothing maps to 0).
The proof that `f` is injective is trivial: `a + 1 = b + 1` implies
`a = b`. But the image of `f` is `{1, 2, 3, ...}` — the element `0`
has no preimage. The counting argument breaks because the 'image has
fewer elements than the source' step has no meaning when both sets
are infinite. Finiteness is essential — it's what makes the
cardinality comparison well-defined.

This theorem connects the two great themes of Phases 1-3:
- **Phase 1** (Fin): elements of finite types
- **Phase 2** (Finset): sets and their operations
- **Phase 3** (Cardinality): counting as a proof technique

The counting argument (pigeonhole + image = univ) proves something
that case analysis cannot scale to: this holds for ALL `n`, not
just `n = 5`.
"

NewTheorem Finset.eq_of_subset_of_card_le

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Fintype.surjective_of_injective Fintype.injective_iff_surjective Fintype.injective_iff_bijective Fintype.surjective_iff_bijective Finset.map_eq_of_subset Finset.eq_univ_of_card
