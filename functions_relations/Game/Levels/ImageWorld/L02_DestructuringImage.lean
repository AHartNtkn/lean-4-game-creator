import Game.Metadata

World "ImageWorld"
Level 2

Title "Destructuring Image Membership"

TheoremTab "Set"

Introduction "
# Working With Image Hypotheses

In Level 1, you CONSTRUCTED image membership -- exhibiting a witness
to prove `y ∈ f '' s`. Now you will DESTRUCTURE an image hypothesis.

If you know `hy : y ∈ f '' s`, this encodes `∃ x, x ∈ s ∧ f x = y`.
Use `obtain` to extract the components:

```
obtain ⟨x, hx, hfx⟩ := hy
```

This gives you:
- `x : α` -- the preimage witness
- `hx : x ∈ s` -- proof that `x` is in `s`
- `hfx : f x = y` -- the equation connecting `x` to `y`

This is **nested destructuring**: the `∃` gives a pair, and the `∧`
inside gives another pair. The pattern `⟨x, hx, hfx⟩` flattens both.

**Your task**: If `y` is in the image of the \"double\" function on
numbers less than 5, prove that `y` is even.
"

/-- If y is the double of some n < 5, then y is even. -/
Statement (y : ℕ) (hy : y ∈ (fun n : ℕ => 2 * n) '' {n | n < 5}) :
    Even y := by
  Hint "You have `hy : y ∈ (fun n => 2 * n) '' ...`. This means
  there exists some `x` in the source set such that `2 * x = y`.
  Destructure with `obtain ⟨x, hx, hfx⟩ := hy`.

  Remember the angle brackets: type ⟨ as `\\<` and ⟩ as `\\>`."
  Hint (hidden := true) "`obtain ⟨x, hx, hfx⟩ := hy` gives you
  `x : ℕ`, `hx : x < 5`, and `hfx : 2 * x = y`."
  obtain ⟨x, hx, hfx⟩ := hy
  Hint "Now `hfx : (fun n => 2 * n) x = y`. The goal is `Even y`. Since
  `y = 2 * x`, rewrite to replace `y` with `2 * x` using `rw [← hfx]`."
  Hint (hidden := true) "`rw [← hfx]` changes the goal to `Even (2 * x)`.
  Then `show Even (2 * x)` to simplify, `use x`, and `omega` finishes."
  rw [← hfx]
  Hint "The goal looks like `Even (2 * x)` but Lean internally still has
  the function form. Use `show Even (2 * x)` to make it explicit."
  show Even (2 * x)
  Hint "Now use `use x` to provide the witness for `Even`, then `omega`."
  use x
  Hint "`omega` closes the arithmetic goal `2 * x = x + x`."
  omega

Conclusion "
You destructured an image hypothesis with
`obtain ⟨x, hx, hfx⟩ := hy`:

- `x : ℕ` -- the preimage witness
- `hx : x < 5` -- membership in the source set
- `hfx : 2 * x = y` -- the mapping equation

Then `rw [← hfx]` replaced `y` with `2 * x` in the goal, and
`use x; omega` proved that `2 * x` is even.

**The image destructuring pattern**: Every time you have a hypothesis
`h : y ∈ f '' s`, use `obtain ⟨x, hx, hfx⟩ := h` to extract:
1. The preimage witness `x`
2. Its membership proof `hx : x ∈ s`
3. The mapping equation `hfx : f x = y`

This pattern is central to image proofs. You will use it constantly.

**Foreshadowing**: In the next level, you will learn `rintro` -- a
power tool that combines `intro` and `obtain` in a single step, with
an even more powerful feature: automatic substitution via `rfl`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem
