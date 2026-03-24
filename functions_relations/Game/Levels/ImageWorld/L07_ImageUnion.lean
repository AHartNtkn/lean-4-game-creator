import Game.Metadata

World "ImageWorld"
Level 7

Title "Image Preserves Union"

TheoremTab "Set"

Introduction "
# Image Distributes Over Union

Here is the first major structural result for images:

$$f(s \\cup t) = f(s) \\cup f(t)$$

Why does this work? Image involves `∃`, and existentials distribute
over disjunction. If `y ∈ f '' (s ∪ t)`, there exists `x ∈ s ∪ t`
with `f x = y`. Since `x ∈ s ∨ x ∈ t`, the SAME witness `x` places
`y` in either `f '' s` or `f '' t`.

Compare with preimage: `f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t` also
held, because `∨` passes through function application. Image preserves
union for a different reason: `∃` distributes over `∨`.

**Proof plan**:
1. `ext y` then `constructor` -- standard set equality structure
2. **Forward**: destructure image of union, case-split on membership,
   place the witness in the correct image
3. **Backward**: case-split on the union of images, destructure each
   case, repackage with union membership
"

/-- Image distributes over union. -/
Statement (α β : Type) (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  Hint "Start with `ext y` then `constructor` as in every set equality proof."
  ext y
  constructor
  -- Forward: y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t
  · Hint "**Forward**: `y ∈ f '' (s ∪ t)` means there exists `x ∈ s ∪ t`
    with `f x = y`. Use `rintro ⟨x, hx, rfl⟩` to destructure."
    Hint (hidden := true) "After `rintro ⟨x, hx, rfl⟩`, case-split on
    `hx` with `cases hx with | inl hs | inr ht`."
    Branch
      intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      cases hx with | inl hs | inr ht
      · left
        exact ⟨x, hs, rfl⟩
      · right
        exact ⟨x, ht, rfl⟩
    rintro ⟨x, hx, rfl⟩
    Hint "`hx : x ∈ s ∪ t` is a disjunction (`x ∈ s ∨ x ∈ t`). Use
    `cases hx with | inl hs | inr ht` to split into cases."
    cases hx with | inl hs | inr ht
    · Hint "`hs : x ∈ s`. The goal is `f x ∈ f '' s ∪ f '' t`. Use
      `left` to target `f '' s`, then construct the image membership."
      Hint (hidden := true) "`left` then `exact ⟨x, hs, rfl⟩`."
      left
      exact ⟨x, hs, rfl⟩
    · Hint "`ht : x ∈ t`. Use `right` to target `f '' t`, then
      construct the image membership."
      Hint (hidden := true) "`right` then `exact ⟨x, ht, rfl⟩`."
      right
      exact ⟨x, ht, rfl⟩
  -- Backward: y ∈ f '' s ∪ f '' t → y ∈ f '' (s ∪ t)
  · Hint "**Backward**: `y ∈ f '' s ∪ f '' t` is a disjunction. Use
    `intro hy` then `cases hy with | inl h | inr h` to split.

    **Alternative**: `rcases` can split the disjunction AND destructure
    each image membership in one step:
    `intro hy` then `rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩`."
    Hint (hidden := true) "In each case, destructure the image membership
    with `obtain ⟨x, hx, rfl⟩ := h`, then build the image of the union."
    intro hy
    Branch
      rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · exact ⟨x, Or.inl hx, rfl⟩
      · exact ⟨x, Or.inr hx, rfl⟩
    cases hy with | inl h | inr h
    · Hint "`h : y ∈ f '' s`. Destructure with `obtain ⟨x, hx, rfl⟩ := h`."
      obtain ⟨x, hx, rfl⟩ := h
      Hint "Now provide the witness `x` in the image of `s ∪ t`.
      Since `hx : x ∈ s`, the union membership is `Or.inl hx`."
      Hint (hidden := true) "`exact ⟨x, Or.inl hx, rfl⟩`

      Or step by step: `use x`, `constructor`,
      `left; exact hx`, `rfl`."
      Branch
        use x
        constructor
        · left; exact hx
        · rfl
      exact ⟨x, Or.inl hx, rfl⟩
    · Hint "`h : y ∈ f '' t`. Destructure and repackage symmetrically."
      Hint (hidden := true) "`obtain ⟨x, hx, rfl⟩ := h` then
      `exact ⟨x, Or.inr hx, rfl⟩`."
      obtain ⟨x, hx, rfl⟩ := h
      Branch
        use x
        constructor
        · right; exact hx
        · rfl
      exact ⟨x, Or.inr hx, rfl⟩

Conclusion "
You proved `f '' (s ∪ t) = f '' s ∪ f '' t`. Image distributes over
union!

The key moves:
- **Forward**: Destructure image of union, case-split on `∈ s ∨ ∈ t`,
  place the same witness in the correct image
- **Backward**: Case-split on `∈ f '' s ∨ ∈ f '' t`, destructure
  each image membership, repackage with `Or.inl`/`Or.inr`

**The witness transfer pattern again**: Both directions re-use the
SAME witness `x` -- you destructure to find it, then repackage it
with updated membership. In the forward direction, `x ∈ s ∪ t`
becomes `x ∈ s` or `x ∈ t`. In the backward direction, `x ∈ s`
or `x ∈ t` becomes `Or.inl hx` or `Or.inr hx` for `x ∈ s ∪ t`.

**`rcases` on disjunctions**: The backward direction could also be
done with `rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩`, which
splits the union of images AND destructures each image membership
in one step. The `|` in `rcases` handles `∨`, just as `⟨...⟩`
handles `∃` and `∧`.

**`Or.inl` and `Or.inr`**: When building anonymous constructors for
unions, `Or.inl hx` injects into the left side and `Or.inr hx` into
the right. The alternative is `left; exact hx` / `right; exact hx`.

**Why this works**: `∃` distributes over `∨`. If `∃ x, (P x ∨ Q x)`,
then `(∃ x, P x) ∨ (∃ x, Q x)`, and vice versa. The union is `∨`
at the predicate level, and image is `∃` at the membership level.

**Scoreboard**:

| Operation | Preimage | Image |
|---|---|---|
| `∪` (union) | ✓ equality | ✓ equality |
| `∩` (intersection) | ✓ equality | ? |

Next: What about intersection?

The library name is `Set.image_union`.
"

/-- `Set.image_union` states `f '' (s ∪ t) = f '' s ∪ f '' t`.
Image distributes over union. -/
TheoremDoc Set.image_union as "Set.image_union" in "Set"

NewTheorem Set.image_union

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_union Iff.rfl
