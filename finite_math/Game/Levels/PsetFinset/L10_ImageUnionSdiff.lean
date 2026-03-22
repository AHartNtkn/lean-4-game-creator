import Game.Metadata

World "PsetFinset"
Level 10

Title "Image, Union, and Set Difference"

Introduction "
# Union + Image + Sdiff Integration

Prove that removing the image of $s$ from the image of $s \\cup t$
leaves only elements from the image of $t$:

$$f(s \\cup t) \\setminus f(s) \\;\\subseteq\\; f(t)$$

This integrates moves from FinsetOperations and FinsetImage:
subset, sdiff, union, image backward/forward, cases, and by_contra.

The interesting case: when the witness came from $s$, you can
build $y \\in f(s)$, which contradicts $y \\notin f(s)$.
"

/-- Elements in the image of a union but not in the image of s must come from t. -/
Statement (f : ℕ → ℕ) (s t : Finset ℕ) :
    (s ∪ t).image f \ s.image f ⊆ t.image f := by
  rw [Finset.subset_iff]
  intro y hy
  rw [Finset.mem_sdiff] at hy
  obtain ⟨hut, hns⟩ := hy
  Hint "Extract the witness from `hut` using backward image membership,
  then determine whether the witness came from `s` or `t`."
  rw [Finset.mem_image] at hut
  obtain ⟨x, hx, hfx⟩ := hut
  rw [Finset.mem_union] at hx
  Hint (hidden := true) "Case-split on `hx` with `cases hx with`.
  In the `inl` case (`x ∈ s`): use `by_contra` then `apply hns`
  to show `y ∈ s.image f`, contradicting `hns`.
  In the `inr` case (`x ∈ t`): build forward membership directly."
  cases hx with
  | inl hxs =>
    by_contra _
    apply hns
    rw [Finset.mem_image]
    exact ⟨x, hxs, hfx⟩
  | inr hxt =>
    rw [Finset.mem_image]
    exact ⟨x, hxt, hfx⟩

Conclusion "
This proof integrated 6 moves from two worlds:

| Move | Source |
|---|---|
| `rw [Finset.subset_iff]; intro y hy` | FinsetOperations |
| `rw [Finset.mem_sdiff] at hy` | FinsetOperations |
| `rw [Finset.mem_image] at hut; obtain ...` | FinsetImage |
| `rw [Finset.mem_union] at hx; cases ...` | FinsetOperations |
| `by_contra; apply hns` | FinsetOperations |
| `rw [Finset.mem_image]; exact ⟨x, ...⟩` | FinsetImage |

The `inl` case used `by_contra` to expose the contradiction:
if $x \\in s$, then $y = f(x) \\in f(s)$, contradicting $y \\notin f(s)$.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_union Finset.image_subset_iff Finset.subset_union_left Finset.subset_union_right Finset.mem_union_left Finset.mem_union_right le_sup_left le_sup_right sdiff_le_self Finset.sdiff_subset sdiff_le
