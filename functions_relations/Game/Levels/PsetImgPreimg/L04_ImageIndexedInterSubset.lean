import Game.Metadata

World "PsetImgPreimg"
Level 4

Title "Image of Indexed Intersection"

TheoremTab "Set"

Introduction "
# Image of ⋂ is Only ⊆ ⋂ of Images

In Preimage World, you proved that preimage distributes over indexed
union AND indexed intersection — both as equalities.

For image, the story is different. You proved `f '' (s \\cup t) = f '' s \\cup f '' t`
(equality), but `f '' (s \\cap t) \\subseteq f '' s \\cap f '' t` (only subset).

Now extend this to indexed intersection:

$$f\\left(\\bigcap_i s_i\\right) \\subseteq \\bigcap_i f(s_i)$$

Why only ⊆? The same reason as the binary case: the image uses an
existential, and a single witness for the intersection of all `s_i`
is stronger than separate witnesses for each `f '' (s_i)`.

**Proof plan**: Take `y \\in f '' (\\bigcap_i s_i)`, destructure to get
a witness `x \\in \\bigcap_i s_i`. Then for each `i`, `x \\in s_i`, so
`f x \\in f '' (s_i)`. Use `Set.mem_iInter` to convert between
indexed intersection membership and universal quantification.
"

/-- Image of indexed intersection is a subset of the indexed
intersection of images. -/
Statement (α β ι : Type) (f : α → β) (s : ι → Set α) :
    f '' (⋂ i, s i) ⊆ ⋂ i, f '' (s i) := by
  Hint "Destructure the image membership, then convert the indexed
  intersection goal/hypothesis with `rw [Set.mem_iInter]`."
  Hint (hidden := true) "`rintro y ⟨x, hx, rfl⟩` then
  `rw [Set.mem_iInter]` then `intro i` then
  `rw [Set.mem_iInter] at hx` then `exact ⟨x, hx i, rfl⟩`."
  Branch
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter] at hx
    exact ⟨x, hx i, rfl⟩
  rintro y ⟨x, hx, rfl⟩
  rw [Set.mem_iInter]
  intro i
  rw [Set.mem_iInter] at hx
  exact ⟨x, hx i, rfl⟩

Conclusion "
You proved `f '' (\\bigcap_i s_i) \\subseteq \\bigcap_i f '' (s_i)`.

The proof used ONE witness `x` from `\\bigcap_i s_i`, which belongs to
ALL `s_i` simultaneously. For each index `i`, the same `x` serves as
witness for `f x \\in f '' (s_i)`.

**Why equality fails**: The reverse direction would require: given
separate witnesses `x_i \\in s_i` for each `i` (all with `f x_i = y`),
finding a single `x \\in \\bigcap_i s_i` with `f x = y`. If `f` is not
injective, the witnesses `x_i` might all be different, and no single
`x` might be in every `s_i`.

**Concrete counterexample**: Let `f(n) = n mod 2`, with `s_0 = {0, 1}`
and `s_1 = {2, 3}` (indexed by `{0, 1}`). Then `\\bigcap_i s_i = \\emptyset`
(no element is in both), so `f '' (\\bigcap_i s_i) = \\emptyset`. But
`f '' s_0 = {0, 1}` and `f '' s_1 = {0, 1}`, so
`\\bigcap_i f '' (s_i) = {0, 1}`. The strict inclusion
`\\emptyset \\subsetneq {0, 1}` shows equality fails. The outputs `0`
and `1` appear in every `f '' (s_i)` via DIFFERENT witnesses, but no
single witness belongs to every `s_i`.

**The pattern**: This is the indexed version of the same phenomenon:

| Operation | Preimage | Image |
|---|---|---|
| Binary `\\cap` | = | only \\subseteq |
| Indexed `\\bigcap` | = | only \\subseteq |
| Binary `\\cup` | = | = |
| Indexed `\\bigcup` | = | = |

The next level proves the indexed union case — the `=` in the last
row. Image preserves ALL unions (binary and indexed) as equalities,
but only \\subseteq for intersections.

The library name is `Set.image_iInter_subset`.
"

/-- `Set.image_iInter_subset` states
`f '' (\\bigcap i, s i) \\subseteq \\bigcap i, f '' (s i)`.
Image of indexed intersection is contained in the indexed
intersection of images. -/
TheoremDoc Set.image_iInter_subset as "Set.image_iInter_subset" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_iInter_subset Iff.rfl
