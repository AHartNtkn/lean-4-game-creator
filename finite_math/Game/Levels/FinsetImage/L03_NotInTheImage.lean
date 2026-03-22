import Game.Metadata

World "FinsetImage"
Level 3

Title "Not in the Image"

Introduction "
# Proving Non-Membership in an Image

Sometimes you need to prove that an element is **not** in the image.
The strategy: assume it IS in the image, extract the witness, and
derive a contradiction from the constraints.

`Finset.mem_image` works in BOTH directions:
- **Forward**: `rw [Finset.mem_image]` on a goal converts `y ∈ image f s`
  to an existential
- **Backward**: `rw [Finset.mem_image] at h` on a hypothesis converts
  `h : y ∈ image f s` to `h : ∃ x ∈ s, f x = y`

After rewriting a hypothesis, use `obtain` to destructure the
existential:
```
obtain ⟨x, hx, hfx⟩ := h
-- x : ℕ, hx : x ∈ s, hfx : f x = y
```

**Your task**: Prove $7 \\notin \\text{image}(n \\mapsto 2n,\\; \\{0,1,2,3\\})$.

The image contains only even numbers (0, 2, 4, 6), and 7 is odd.
If $2x = 7$ had a solution in $\\{0,1,2,3\\}$, we'd need $x = 3.5$
— impossible for a natural number.
"

/-- 7 is not in the image of (n ↦ 2 * n) on range 4. -/
Statement : (7 : ℕ) ∉ (Finset.range 4).image (fun n => 2 * n) := by
  Hint "The goal is `7 ∉ ...`, which means `7 ∈ ... → False`.
  Use `intro h` to assume `7` IS in the image and aim for
  a contradiction."
  intro h
  Hint "Now `h : 7 ∈ (Finset.range 4).image (fun n => 2 * n)`.
  Use `rw [Finset.mem_image] at h` to unwrap the existential."
  rw [Finset.mem_image] at h
  Hint "Now `h : ∃ x ∈ Finset.range 4, 2 * x = 7`.
  Use `obtain ⟨x, hx, hfx⟩ := h` to extract the witness
  and its properties."
  obtain ⟨x, hx, hfx⟩ := h
  Hint "You have:
  - `hx : x ∈ Finset.range 4` (i.e., `x < 4`)
  - `hfx : 2 * x = 7`

  Rewrite `hx` with `rw [Finset.mem_range] at hx` to get the
  bound, then `omega` sees that `x < 4` and `2 * x = 7` is impossible."
  rw [Finset.mem_range] at hx
  Hint (hidden := true) "`omega` can close this: `x < 4` and `2 * x = 7`
  has no natural number solution (7 is odd)."
  omega

Conclusion "
The non-membership pattern for images:
1. `intro h` — assume membership
2. `rw [Finset.mem_image] at h` — unwrap the existential
3. `obtain ⟨x, hx, hfx⟩ := h` — extract the witness
4. Derive a contradiction from the witness constraints

This is the **backward extraction** move: given `y ∈ image f s`,
you get a concrete witness `x` with its membership proof `x ∈ s`
and functional equation `f x = y`.

In plain math: to show $y \\notin f(S)$, show that $f(x) = y$ has
no solution in $S$.

You'll use this backward extraction move whenever you have an
image membership as a *hypothesis* (not a goal).
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
