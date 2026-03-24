import Game.Metadata

World "PsetImgPreimg"
Level 10

Title "Boss: Injectivity Closes the Preimage-Image Gap"

TheoremTab "Set"

Introduction "
# Boss: f ⁻¹' (f '' s) = s for Injective f

In Image World, you proved two gap results:
- `f '' (f ⁻¹' t) \\subseteq t` — equality needs surjectivity (L14)
- `s \\subseteq f ⁻¹' (f '' s)` — equality needs injectivity (L15)

The boss of Image World closed the FIRST gap (with a surjectivity
condition). Now you will close the SECOND gap:

$$\\text{Injective}(f) \\;\\Longrightarrow\\; f^{-1}(f(s)) = s$$

The \\supseteq direction (`s \\subseteq f ⁻¹' (f '' s)`) is what you
proved in Image World L15 — it holds unconditionally. You will
recognize it as a retrieval exercise from that world.

The \\subseteq direction (`f ⁻¹' (f '' s) \\subseteq s`) is where
injectivity is needed — this is the **witness collapse** pattern
one last time. If `x \\in f ⁻¹' (f '' s)`, then `f x \\in f '' s`,
so there exists `a \\in s` with `f a = f x`. Injectivity collapses
`a` and `x` into one, giving `x \\in s`.

**Skills required**:
- `ext` + `constructor` for set equality
- Image membership destructuring (`obtain ⟨a, ha, hfa⟩`)
- Preimage membership unfolding (definitional)
- Applying `Function.Injective`
- Image membership construction (`⟨x, hx, rfl⟩`)
"

/-- The preimage-image roundtrip is the identity for injective
functions. -/
Statement (α β : Type) (f : α → β) (s : Set α)
    (hinj : Function.Injective f) :
    f ⁻¹' (f '' s) = s := by
  ext x
  constructor
  -- Forward: x ∈ f ⁻¹' (f '' s) → x ∈ s
  · Hint "**Forward (the hard direction)**: `x \\in f ⁻¹' (f '' s)`
    means `f x \\in f '' s`. Extract the witness, apply injectivity
    to collapse it with `x`, and conclude."
    Hint (hidden := true) "`intro hx` then `obtain ⟨a, ha, hfa⟩ := hx`
    then `have hax := hinj hfa` then `rw [hax] at ha` then
    `exact ha`."
    Branch
      -- Alternative if obtain doesn't see through the preimage
      intro hx
      change f x ∈ f '' s at hx
      obtain ⟨a, ha, hfa⟩ := hx
      have hax := hinj hfa
      rw [hax] at ha
      exact ha
    intro hx
    obtain ⟨a, ha, hfa⟩ := hx
    have hax := hinj hfa
    rw [hax] at ha
    exact ha
  -- Backward: x ∈ s → x ∈ f ⁻¹' (f '' s)
  · Hint "**Backward (the easy direction)**: Build `f x \\in f '' s`
    with witness `x`."
    Hint (hidden := true) "`intro hx` then `exact ⟨x, hx, rfl⟩`."
    intro hx
    exact ⟨x, hx, rfl⟩

Conclusion "
Congratulations — you completed the **Image & Preimage Problem Set**!

The boss combined every core skill from Preimage World and Image World.

**Forward direction** (injectivity needed — the **witness collapse** pattern):
```
intro hx
obtain ⟨a, ha, hfa⟩ := hx
have hax := hinj hfa
rw [hax] at ha
exact ha
```
This is the same witness collapse you used in Levels 7, 8, and 9:
extract two witnesses, apply injectivity to collapse them into one.

**Backward direction** (unconditional — review from Image World L15):
```
intro hx
exact ⟨x, hx, rfl⟩
```

## The Two Gap Closures

You have now seen both gap closures:

| Gap | Statement | Closes with |
|---|---|---|
| Image-preimage | `f '' (f ⁻¹' t) = t` | Surjectivity (`t \\subseteq range f`) |
| Preimage-image | `f ⁻¹' (f '' s) = s` | Injectivity |

These are deep results. Injectivity means the function does not
collapse inputs — so pulling back and pushing forward recovers the
original set. Surjectivity means the function hits everything —
so pushing forward and pulling back recovers the original set.

**The duality**: Injectivity closes the preimage-image gap
(`f ⁻¹' (f '' s) = s`), and surjectivity closes the image-preimage
gap (`f '' (f ⁻¹' t) = t`). These are perfectly dual: one says the
function \"doesn't merge,\" the other says the function \"doesn't miss.\"
Together, they tell you exactly what properties of `f` control each
roundtrip.

If `f` is **bijective** (both injective and surjective), BOTH
roundtrip identities hold: `f ⁻¹' (f '' s) = s` AND
`f '' (f ⁻¹' t) = t`. Image and preimage become true inverses on
the powerset. You will explore this fully in Bijective World.

## Complete Operations Table

| Operation | Image (no injectivity) | Image (with injectivity) | Preimage |
|---|---|---|---|
| Binary \\cap | only \\subseteq | **=** | = |
| Indexed \\bigcap | only \\subseteq | **=** | = |
| Binary \\cup | = | = | = |
| Indexed \\bigcup | = | = | = |
| Set difference \\\\ | only \\supseteq | **=** | = |
| Roundtrip with preimage | only \\supseteq | **=** | n/a |
| Roundtrip with image | n/a | n/a | only \\subseteq (= with surjectivity) |

The pattern: preimage preserves everything. Image preserves unions
but only \\subseteq for intersections and \\supseteq for differences
and roundtrips. Injectivity closes every gap in the image column.

## Summary of the Problem Set

| Level | Statement | Key skill |
|---|---|---|
| 1 | `f '' s \\subseteq Set.range f` | Image \\to range |
| 2 | `Nat.succ '' ...` concrete computation | Grounding the abstraction |
| 3 | `f '' (s \\cap f ⁻¹' t) = f '' s \\cap t` | Combining image + preimage |
| 4 | `f '' (\\bigcap_i s_i) \\subseteq \\bigcap_i f '' (s_i)` | Indexed intersection + image |
| 5 | `f '' (\\bigcup_i s_i) = \\bigcup_i f '' (s_i)` | Indexed union + image |
| 6 | `f '' s \\\\ f '' t \\subseteq f '' (s \\\\ t)` | Contradiction reasoning |
| 7 | Injective \\to binary intersection gap closes | Witness collapse |
| 8 | Injective \\to indexed intersection gap closes | Indexed witness collapse |
| 9 | Injective \\to set difference becomes equality | Witness collapse + contradiction |
| 10 | Injective \\to preimage-image gap closes | Full integration |

**Looking ahead**: In Injective World, you will prove injectivity
for specific functions, compose injections, and connect injectivity
to left inverses. In Surjective World, you will do the same for
surjectivity and right inverses. The gap closure results you proved
here are the bridge between image/preimage theory and function
properties.
"

/-- `Set.preimage_image_eq` states that if `f` is injective,
then `f ⁻¹' (f '' s) = s`. The preimage-image roundtrip is the
identity for injective functions. -/
TheoremDoc Set.preimage_image_eq as "Set.preimage_image_eq" in "Set"

/-- `Function.Injective.preimage_image` states that if `f` is
injective, then `f ⁻¹' (f '' s) = s`. Alias for
`Set.preimage_image_eq`. -/
TheoremDoc Function.Injective.preimage_image as "Function.Injective.preimage_image" in "Function"

/-- `Set.subset_preimage_image` states `s ⊆ f ⁻¹' (f '' s)`. Every
element of `s` is in the preimage of the image. Disabled to force
manual proof in the boss. -/
TheoremDoc Set.subset_preimage_image as "Set.subset_preimage_image" in "Set"

/-- `Set.image_preimage_subset` states `f '' (f ⁻¹' t) ⊆ t`. Applying
the function to the preimage gives back a subset of the original.
Disabled to force manual proof in the boss. -/
TheoremDoc Set.image_preimage_subset as "Set.image_preimage_subset" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.preimage_image_eq Function.Injective.preimage_image Set.subset_preimage_image Set.image_preimage_subset Iff.rfl
