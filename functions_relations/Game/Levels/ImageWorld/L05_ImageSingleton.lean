import Game.Metadata

World "ImageWorld"
Level 5

Title "Image of a Singleton"

TheoremTab "Set"

Introduction "
# The Simplest Image: One Element In, One Element Out

Before tackling abstract structural results, let us ground the image
definition on the absolute simplest case: the image of a **singleton
set**.

If `s` contains only elements equal to `a`, then the image of `s`
under `f` contains only elements equal to `f a`.

$$f(\\{a\\}) = \\{f(a)\\}$$

This is almost obvious, but the proof exercises the same witness
construction and destructuring patterns you have been learning --
on a case where the witness is always `a` and the membership
proof is always `rfl`. Think of it as a warm-up before the abstract
proofs ahead.

**Proof plan**:
1. `ext y` then `constructor`
2. **Forward**: Destructure `y ∈ f '' s`. The witness satisfies
   `x ∈ s`, which means `x = a`. Substitute to get `y = f a`.
3. **Backward**: `y = f a` means we can provide witness `a`.
"

/-- The image of a singleton is the singleton of the image. -/
Statement (α β : Type) (f : α → β) (a : α) :
    f '' {x | x = a} = {y | y = f a} := by
  Hint "Start with `ext y` then `constructor` as usual for set equality."
  ext y
  constructor
  -- Forward: y ∈ f '' {x | x = a} → y ∈ {y | y = f a}
  · Hint "**Forward**: `y ∈ f '' ...` means there exists some `x` with
    `x = a` and `f x = y`. Use `rintro ⟨x, hx, rfl⟩` to destructure."
    Hint (hidden := true) "After `rintro ⟨x, hx, rfl⟩`, you have
    `hx : x = a` and the goal is `f x = f a`.
    Use `show f x = f a` then `rw [hx]`."
    Branch
      intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      show f x = f a
      rw [hx]
    rintro ⟨x, hx, rfl⟩
    Hint "You have `hx : x = a` (membership in the singleton) and the
    goal is `f x = f a`. Use `show f x = f a` to make this explicit,
    then `rw [hx]` to substitute `a` for `x`."
    Hint (hidden := true) "`show f x = f a` then `rw [hx]`."
    show f x = f a
    rw [hx]
  -- Backward: y ∈ {y | y = f a} → y ∈ f '' {x | x = a}
  · Hint "**Backward**: `y = f a`. Use `intro hy` to get this fact."
    Hint (hidden := true) "`intro hy` then `rw [hy]`,
    `exact ⟨a, rfl, rfl⟩`."
    intro hy
    Hint "`hy : y = f a`. Rewrite with `rw [hy]` to replace `y`
    with `f a` in the goal."
    rw [hy]
    Hint "Now the goal is `f a ∈ f '' ...`. The witness is `a`:
    it satisfies `a = a` (membership) and `f a = f a` (equation)."
    Hint (hidden := true) "`exact ⟨a, rfl, rfl⟩`"
    exact ⟨a, rfl, rfl⟩

Conclusion "
You proved that the image of a singleton is the singleton of the
image!

This is the simplest concrete instance of the image definition.
The witness is always `a`, the membership proof is always `rfl`,
and the equation is always `rfl`. No choices, no case analysis --
just the pure existential witness pattern in its most basic form.

**Pattern check**: Compare with Level 1 where you proved a specific
element was in an image. Here the witness was obvious (`a`), but
the proof structure was identical: provide the witness, prove
membership in the source set, prove the equation.

**Foreshadowing**: Singleton images appear in injectivity proofs.
If `f` is injective and the images of two singletons are equal,
then the singletons themselves must be equal. The singleton case
connects images to the element-level behavior of functions.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Set.image_singleton
