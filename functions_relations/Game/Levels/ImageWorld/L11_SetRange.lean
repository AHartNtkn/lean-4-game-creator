import Game.Metadata

World "ImageWorld"
Level 11

Title "Set.range: The Image of Everything"

TheoremTab "Set"

Introduction "
# The Range of a Function

The **range** of a function `f : α → β` is the set of ALL outputs:

$$\\text{range}(f) = \\{y \\mid \\exists\\, x,\\; f(x) = y\\}$$

In Lean, this is `Set.range f`. The membership rule is:

$$y \\in \\text{range}(f) \\;\\;\\Longleftrightarrow\\;\\; \\exists\\, x,\\; f(x) = y$$

This is `Set.mem_range`. Notice it is just like image membership
but WITHOUT the source set constraint. Equivalently,
`Set.range f = f '' Set.univ` -- the image of the universal set.

**Your task**: Prove that the range of the doubling function is
exactly the set of even numbers:
`Set.range (fun n : ℕ => 2 * n) = {n | Even n}`.

**Proof plan**:
1. `ext y` then `constructor`
2. **Forward**: `rintro ⟨x, rfl⟩` gives `x` and substitutes `y = 2 * x`.
   Prove `Even (2 * x)` with `use x; omega`.
3. **Backward**: `intro hy` gets `hy : Even y`. Destructure the
   existential to find the witness, then construct range membership.
"

/-- The range of the doubling function is exactly the even numbers. -/
Statement : Set.range (fun n : ℕ => 2 * n) = {n | Even n} := by
  Hint "Start with `ext y` then `constructor` as usual."
  ext y
  constructor
  -- Forward: y ∈ range (2 * ·) → Even y
  · Hint "**Forward**: `y ∈ Set.range (fun n => 2 * n)` means
    `∃ x, 2 * x = y`. Use `rintro ⟨x, rfl⟩` to get `x` and
    substitute `y = 2 * x`.

    Note: range membership has only TWO components (witness and
    equation), not three like image membership."
    Hint (hidden := true) "`rintro ⟨x, rfl⟩` then `show Even (2 * x)`,
    `use x`, `omega`."
    Branch
      intro hy
      obtain ⟨x, rfl⟩ := hy
      show Even (2 * x)
      use x
      omega
    rintro ⟨x, rfl⟩
    Hint "The goal says `Even (2 * x)` but Lean internally has the function
    form. Use `show Even (2 * x)` to make it explicit."
    show Even (2 * x)
    Hint "Now `Even (2 * x)` means `∃ r, 2 * x = r + r`. The witness
    is `x`. Use `use x` then `omega`."
    use x
    omega
  -- Backward: Even y → y ∈ range (2 * ·)
  · Hint "**Backward**: `Even y` means `∃ r, y = r + r`. Use
    `intro hy` then `obtain ⟨r, hr⟩ := hy` to get the witness."
    Hint (hidden := true) "After obtaining `r` and `hr : y = r + r`,
    use `use r`, `show 2 * r = y`, `omega`."
    intro hy
    Hint "Destructure `hy : Even y` with `obtain ⟨r, hr⟩ := hy`
    to get the witness `r` and equation `hr : y = r + r`."
    obtain ⟨r, hr⟩ := hy
    Hint "Now build range membership: you need `∃ x, 2 * x = y`.
    The witness is `r`. Use `use r`."
    use r
    Hint "The goal is `2 * r = y` (the function applied to the witness
    equals `y`). Use `show 2 * r = y` to make this explicit, then `omega`."
    show 2 * r = y
    omega

Conclusion "
You proved `Set.range (fun n => 2 * n) = {n | Even n}`.

**Range vs Image**: `Set.range f` is the same as `f '' Set.univ` --
the image of the universal set. Range membership has the simpler form
`∃ x, f x = y` (no source set constraint), while image membership
is `∃ x, x ∈ s ∧ f x = y`.

**The `rintro ⟨x, rfl⟩` pattern for range**: Since range membership
has only two components (witness + equation), the destructuring
pattern is `⟨x, rfl⟩` instead of `⟨x, hx, rfl⟩`. The `rfl`
substitutes `y = f x` just as before.

**Where range appears**: Range is fundamental to surjectivity.
A function `f` is **surjective** if `Set.range f = Set.univ` -- every
element of the codomain is in the range. You will explore this in
Surjective World.

The library name is `Set.mem_range`.
"

/-- `Set.range f`, written `Set.range f`, is the **range** of `f` --
the set of all outputs:

$$\\text{range}(f) = \\{y \\mid \\exists\\, x,\\; f(x) = y\\}$$

## Membership rule
`y ∈ Set.range f ↔ ∃ x, f x = y` (this is `Set.mem_range`)

## Connection to image
`Set.range f = f '' Set.univ`

## Syntax
```
Set.range f      -- the range of f
```

## When to use it
When you want to talk about the set of all possible outputs of `f`,
without restricting to a particular input set.

## Example
`Set.range (fun n : ℕ => 2 * n) = {n | Even n}` -- the range of
the doubling function is the even numbers.
-/
DefinitionDoc Set.range as "Set.range"

/-- `Set.mem_range` states `y ∈ Set.range f ↔ ∃ x, f x = y` --
membership in the range means there is some input that maps to `y`.

## Syntax
```
rw [Set.mem_range]         -- on the goal
rw [Set.mem_range] at h    -- on a hypothesis
```

## When to use it
When you need to convert between `y ∈ Set.range f` and the explicit
existential `∃ x, f x = y`. Often you can work directly with
`rintro ⟨x, rfl⟩` or `obtain ⟨x, rfl⟩` instead.
-/
TheoremDoc Set.mem_range as "Set.mem_range" in "Set"

NewDefinition Set.range
NewTheorem Set.mem_range

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem
