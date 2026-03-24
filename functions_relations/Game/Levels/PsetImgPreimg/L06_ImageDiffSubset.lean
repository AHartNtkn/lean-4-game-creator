import Game.Metadata

World "PsetImgPreimg"
Level 6

Title "Image and Set Difference"

TheoremTab "Set"

Introduction "
# f '' s \\ f '' t ⊆ f '' (s \\ t)

Here is a twist: what happens when you take the DIFFERENCE of two
images?

$$f(s) \\setminus f(t) \\subseteq f(s \\setminus t)$$

In words: if `y` is in the image of `s` but NOT in the image of `t`,
then `y` must come from an element of `s` that is NOT in `t`.

Why? If `y = f x` for some `x \\in s`, and `y \\notin f '' t`, then
no element of `t` maps to `y`. In particular, `x` itself cannot be
in `t` (or else `f x \\in f '' t`, contradicting `y \\notin f '' t`).
So `x \\in s \\setminus t`.

This level requires a small piece of **contradiction reasoning**:
you must show `x \\notin t` by showing that `x \\in t` would create
a contradiction with `y \\notin f '' t`.
"

/-- Elements in the image of s but not the image of t come from
elements of s that are not in t. -/
Statement (α β : Type) (f : α → β) (s t : Set α) :
    f '' s \ f '' t ⊆ f '' (s \ t) := by
  Hint "Destructure `y \\in f '' s \\ f '' t` to get `hxs : x \\in s`
  and `hynt : f x \\notin f '' t`. Then provide witness `x` and show
  `x \\in s \\ t` by proving `x \\notin t` via contradiction."
  Hint (hidden := true) "`rintro y ⟨⟨x, hxs, rfl⟩, hynt⟩` then
  `use x` then `constructor` then `constructor` then `exact hxs`
  then `intro hxt` then `exact hynt ⟨x, hxt, rfl⟩` then `rfl`."
  Branch
    intro y hy
    obtain ⟨hys, hynt⟩ := hy
    obtain ⟨x, hxs, rfl⟩ := hys
    use x
    constructor
    · constructor
      · exact hxs
      · intro hxt
        exact hynt ⟨x, hxt, rfl⟩
    · rfl
  rintro y ⟨⟨x, hxs, rfl⟩, hynt⟩
  use x
  constructor
  · constructor
    · exact hxs
    · intro hxt
      exact hynt ⟨x, hxt, rfl⟩
  · rfl

Conclusion "
You proved `f '' s \\ f '' t \\subseteq f '' (s \\ t)`.

The key insight was the **contrapositive argument**: to show `x \\notin t`,
you assumed `x \\in t` and derived a contradiction via `f x \\in f '' t`.
This is the first time in this problem set that image membership was
used to DERIVE a contradiction rather than to BUILD a witness.

**Why only \\subseteq**: The reverse `f '' (s \\ t) \\subseteq f '' s \\ f '' t`
does NOT hold. Consider `f(n) = 0`, `s = \\{0, 1\\}`, `t = \\{1\\}`:
- `s \\ t = \\{0\\}`, so `f '' (s \\ t) = \\{0\\}`
- `f '' s = \\{0\\}`, `f '' t = \\{0\\}`, so `f '' s \\ f '' t = \\emptyset`
- `\\{0\\} \\not\\subseteq \\emptyset`

A non-injective function can map elements of `t` to the same output
as elements of `s \\ t`, creating outputs in `f '' (s \\ t)` that
also appear in `f '' t`.

**The operations picture so far**:

| Operation | Preimage | Image |
|---|---|---|
| Binary \\cap | = | only \\subseteq |
| Indexed \\bigcap | = | only \\subseteq |
| Binary \\cup | = | = |
| Indexed \\bigcup | = | = |
| Set difference \\\\ | = | only \\supseteq |

Image does not preserve complement in either direction:
`f '' sᶜ` and `(f '' s)ᶜ` have no inclusion relationship in general.

**When does equality hold?** When `f` is injective on `s`. If
different inputs always produce different outputs, no element of
`t` can produce an output that also comes from `s \\ t`.

The library name is `Set.subset_image_diff`.
"

/-- `Set.subset_image_diff` states
`f '' s \\ f '' t \\subseteq f '' (s \\ t)`.
Elements in the image of `s` but not the image of `t` come from
elements of `s \\ t`. -/
TheoremDoc Set.subset_image_diff as "Set.subset_image_diff" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.subset_image_diff Set.image_diff Iff.rfl
