import Game.Metadata

World "ImageWorld"
Level 1

Title "What is an Image?"

TheoremTab "Set"

Introduction "
# Images: Pushing Sets Forward Through Functions

In Preimage World, you pulled sets **backward** through functions:
`x ∈ f ⁻¹' t` meant `f x ∈ t` -- just function application.

Now you will push sets **forward**. The **image** of a set `s`
under `f` is:

$$f(s) = \\{y \\mid \\exists\\, x \\in s,\\; f(x) = y\\}$$

In Lean, this is written `f '' s` (type `''`). The membership rule is:

$$y \\in f\\;'' s \\;\\;\\Longleftrightarrow\\;\\; \\exists\\, x \\in s,\\; f(x) = y$$

This is `Set.mem_image`. Notice the **existential**: to prove something
is in the image, you must **exhibit a witness** -- a specific input `x`
in `s` that maps to `y`. This is fundamentally different from preimage,
which had no existential.

**Your task**: Prove that 4 is in the image of the set of natural numbers
less than 5, under the function `n ↦ n + 1`.

The witness is `n = 3`, because `3 ∈ s` (since `3 < 5`) and `3 + 1 = 4`.

**Proof plan**:
1. `use 3` -- provide the witness
2. `constructor` -- split the conjunction (membership + equation)
3. Prove `3 < 5` with `show` and `omega`
4. Prove `3 + 1 = 4` with `rfl`
"

/-- 4 is in the image because 3 maps to 4 under n ↦ n + 1. -/
Statement : (4 : ℕ) ∈ (fun n : ℕ => n + 1) '' {n | n < 5} := by
  Hint "The goal says `4 ∈ (fun n => n + 1) '' ...`. By the definition
  of image, this means there exists some `x` in the set with
  `x + 1 = 4`. The witness is `x = 3`. Use `use 3`."
  Hint (hidden := true) "`use 3` provides the witness. Then `constructor`
  to split, `show 3 < 5; omega` for the first part, `rfl` for the second."
  use 3
  Hint "After `use 3`, the goal is a conjunction: `3` is in the source
  set AND `3 + 1 = 4`. Use `constructor` to split."
  constructor
  · Hint "The goal asks whether `3` is in the source set. This unfolds
    to `3 < 5`. Use `show 3 < 5` to make this explicit, then `omega`."
    Hint (hidden := true) "`show 3 < 5` then `omega`."
    show 3 < 5
    omega
  · Hint "The goal is `3 + 1 = 4`, which is true by computation.
    Use `rfl`."
    rfl

Conclusion "
You proved your first image membership! The proof was:

1. **Exhibit**: `use 3` -- provide the witness `x = 3`
2. **Split**: `constructor` -- separate membership from equation
3. **Verify membership**: `3 < 5` ✓
4. **Verify equation**: `3 + 1 = 4` ✓

**The key contrast with preimage**: In Preimage World, `3 ∈ f ⁻¹' t`
just meant `f 3 ∈ t` -- a single membership check, no construction.
Image membership `4 ∈ f '' s` requires CONSTRUCTING a witness: you
must name a specific `x`, prove `x ∈ s`, and prove `f x = 4`. The
existential makes image proofs heavier than preimage proofs.

**The `use` tactic**: When the goal is `∃ x, P x`, `use e` substitutes
`x := e` and leaves `P e` as the remaining goal. You saw `use` in Set
World for proving `Even 4`. Here it works the same way: `use 3`
provides the existential witness.

The notation `f '' s` is typed `''` (two single quotes).
"

/-- `Set.image f s`, written `f '' s`, is the **image** of `s`
under `f` -- the set of all outputs produced by inputs in `s`:

$$f(s) = \\{y \\mid \\exists\\, x \\in s,\\; f(x) = y\\}$$

## Membership rule
`y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y` (this is `Set.mem_image`)

## Syntax
```
f '' s      -- image of s under f (type '')
```

## When to use it
When you want to talk about which outputs of `f` come from inputs in `s`.

## Example
If `f n = n + 1`, then `f '' {n | n < 3} = {1, 2, 3}`.

## Warning
`f '' s` is a set of OUTPUTS (type `Set β`), not inputs. Do not
confuse with `f ⁻¹' t` (preimage), which is a set of INPUTS.
-/
DefinitionDoc Set.image as "Set.image"

/-- `Set.mem_image` states `y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y` --
membership in an image means there exists an input in `s` that maps
to `y`.

## Syntax
```
rw [Set.mem_image]         -- on the goal
rw [Set.mem_image] at h    -- on a hypothesis
```

## When to use it
When you need to convert between `y ∈ f '' s` and the explicit
existential form `∃ x, x ∈ s ∧ f x = y`. Often you can work with
image membership directly via `use` (to construct) or `obtain` (to
destructure) without rewriting.

## Example
```
-- Goal: y ∈ f '' s
use x            -- provide the witness
constructor      -- split into x ∈ s and f x = y
```
-/
TheoremDoc Set.mem_image as "Set.mem_image" in "Set"

NewDefinition Set.image
NewTheorem Set.mem_image

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem
