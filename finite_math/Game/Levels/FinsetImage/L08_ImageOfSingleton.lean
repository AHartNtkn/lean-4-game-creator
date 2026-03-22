import Game.Metadata

World "FinsetImage"
Level 8

Title "Image of a Singleton"

Introduction "
# Boundary Cases: What Happens at the Extremes?

A key boundary case for image:

**Singleton**: The image of a singleton $\\{a\\}$ under $f$ is
$\\{f(a)\\}$ — there's exactly one element to map, producing
exactly one output. In Lean: `Finset.image_singleton`.

This is proved in Mathlib, but proving it manually teaches
an important extraction pattern.

**Your task**: Given that `x` is in the image of `{a}` under `f`,
prove that `x = f a`. In other words: the only element in the
image of a singleton is the function applied to that element.

Strategy: extract the witness from `h`, observe it must equal `a`
(the only element), then derive `x = f a`.
"

/-- Every element in the image of a singleton equals f applied to that element. -/
Statement (f : ℕ → ℕ) (a x : ℕ)
    (h : x ∈ ({a} : Finset ℕ).image f) : x = f a := by
  Hint "Extract the witness from `h`. Use `rw [Finset.mem_image] at h`."
  rw [Finset.mem_image] at h
  Hint "Use `obtain ⟨b, hb, hfb⟩ := h` to get the witness `b`,
  its membership `hb : b ∈ singleton a`, and `hfb : f b = x`."
  obtain ⟨b, hb, hfb⟩ := h
  Hint "Now `hb : b ∈ singleton a`. Use `rw [Finset.mem_singleton] at hb`
  to get `hb : b = a`."
  rw [Finset.mem_singleton] at hb
  Hint "You have `hb : b = a` and `hfb : f b = x`. Rewrite `b` to `a`
  in `hfb` using `rw [hb] at hfb`, then use the result."
  Hint (hidden := true) "After `rw [hb] at hfb`, you have `hfb : f a = x`.
  Then `exact hfb.symm` closes the goal."
  rw [hb] at hfb
  exact hfb.symm

Conclusion "
The singleton extraction pattern:
1. Extract the witness: `obtain ⟨b, hb, hfb⟩ := h`
2. Observe the witness is determined: `rw [Finset.mem_singleton] at hb`
3. Substitute and conclude

This confirms: $f(\\{a\\}) = \\{f(a)\\}$. The image of a singleton
is a singleton.

This boundary case anchors the general behavior: image can only
shrink cardinality (by collapsing), never expand it.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_singleton Finset.image_empty
