import Game.Metadata

World "PsetFinset"
Level 13

Title "Non-Membership from Image"

Introduction "
# Contrapositive of Forward Image Membership

If $f(a) \\notin f(s)$, then $a \\notin s$.

The contrapositive: if $a$ WERE in $s$, then $f(a)$ would be in
$f(s)$ (by forward image membership), contradicting the hypothesis.

This is the negation pattern from FinsetOperations applied to
image reasoning from FinsetImage.
"

/-- If f(a) is not in the image of s, then a is not in s. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (a : ℕ) (h : f a ∉ s.image f) :
    a ∉ s := by
  Hint "The goal `a ∉ s` means `a ∈ s → False`.
  Assume `a ∈ s` with `intro ha`, then derive `False`."
  intro ha
  Hint "You have `ha : a ∈ s` and need `False`. If you can show
  `f a ∈ s.image f`, that contradicts `h`."
  Hint (hidden := true) "`apply h`
  `rw [Finset.mem_image]`
  `exact ⟨a, ha, rfl⟩`"
  apply h
  rw [Finset.mem_image]
  exact ⟨a, ha, rfl⟩

Conclusion "
The proof pattern:
1. Assume `a ∈ s` (intro the negation goal)
2. Derive `f a ∈ s.image f` (forward image membership with witness `a`)
3. Contradiction with `h : f a ∉ s.image f`

Compare this to L07 (injective non-membership), which proved
`a ∉ s → f a ∉ s.image f` using injectivity. This level proves
`f a ∉ s.image f → a ∉ s` — no injectivity needed, because the
direction is different. Forward image membership gives the
containment directly.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
