import Game.Metadata

World "PsetImgPreimg"
Level 9

Title "Injectivity Makes Set Difference an Equality"

TheoremTab "Set"

Introduction "
# Injectivity Closes the Set Difference Gap

In Level 6, you proved `f '' s \\ f '' t \\subseteq f '' (s \\ t)` — only
a subset. The reverse direction failed because a non-injective function
can map elements of `t` to the same output as elements of `s \\ t`.

Now prove the **full equality** under the hypothesis that `f` is injective:

$$\\text{Injective}(f) \\;\\Longrightarrow\\; f(s \\setminus t) = f(s) \\setminus f(t)$$

This is a natural companion to Level 7. Both results use the
**witness collapse** pattern: injectivity prevents \"phantom overlap\"
where different inputs produce the same output.

**Proof plan**: `ext y` then `constructor`. The forward direction uses
injectivity via witness collapse; the backward direction is Level 6's
contrapositive argument.
"

/-- Injective functions preserve set difference as equality. -/
Statement (α β : Type) (f : α → β) (s t : Set α)
    (hinj : Function.Injective f) :
    f '' (s \ t) = f '' s \ f '' t := by
  ext y
  constructor
  -- Forward: f '' (s \ t) → f '' s \ f '' t
  · Hint "Destructure to get `x \\in s` and `x \\notin t`. The first
    part (`f x \\in f '' s`) is immediate. For the second, assume
    `f x \\in f '' t`, extract a witness `b \\in t` with `f b = f x`,
    and apply injectivity to reach a contradiction."
    Hint (hidden := true) "`rintro ⟨x, ⟨hxs, hxnt⟩, rfl⟩` then
    `constructor` then `exact ⟨x, hxs, rfl⟩` then `intro hft` then
    `obtain ⟨b, hbt, hbfx⟩ := hft` then `have heq := hinj hbfx` then
    `rw [heq] at hbt` then `exact hxnt hbt`."
    Branch
      intro hy
      obtain ⟨x, ⟨hxs, hxnt⟩, rfl⟩ := hy
      constructor
      · exact ⟨x, hxs, rfl⟩
      · intro hft
        obtain ⟨b, hbt, hbfx⟩ := hft
        have heq := hinj hbfx
        rw [heq] at hbt
        exact hxnt hbt
    rintro ⟨x, ⟨hxs, hxnt⟩, rfl⟩
    constructor
    · exact ⟨x, hxs, rfl⟩
    · intro hft
      obtain ⟨b, hbt, hbfx⟩ := hft
      have heq := hinj hbfx
      rw [heq] at hbt
      exact hxnt hbt
  -- Backward: f '' s \ f '' t → f '' (s \ t)
  · Hint "This is the non-injective direction from Level 6.
    Destructure to get `x \\in s` and `f x \\notin f '' t`, then
    show `x \\notin t` by contradiction."
    Hint (hidden := true) "`rintro ⟨⟨x, hxs, rfl⟩, hfxnt⟩` then
    `use x` then `constructor` then `constructor` then `exact hxs`
    then `intro hxt` then `exact hfxnt ⟨x, hxt, rfl⟩` then `rfl`."
    Branch
      intro hy
      obtain ⟨⟨x, hxs, rfl⟩, hfxnt⟩ := hy
      use x
      constructor
      · constructor
        · exact hxs
        · intro hxt
          exact hfxnt ⟨x, hxt, rfl⟩
      · rfl
    rintro ⟨⟨x, hxs, rfl⟩, hfxnt⟩
    use x
    constructor
    · constructor
      · exact hxs
      · intro hxt
        exact hfxnt ⟨x, hxt, rfl⟩
    · rfl

Conclusion "
You proved that injective functions preserve set difference as equality:
`f '' (s \\ t) = f '' s \\ f '' t` when `f` is injective.

**Forward direction** (injectivity needed):
The key move was the **witness collapse** pattern again — when you have
`f b = f x` and need to derive a contradiction, injectivity gives
`b = x`, collapsing the two witnesses into one.

**Backward direction** (unconditional):
This was Level 6's proof recycled — the contrapositive argument that
`x \\in t` would yield `f x \\in f '' t`.

**Structural insight — proof composition**: This result is not
independent of Level 7's intersection result. Since
`s \\ t = s \\cap t^c`, the equality `f '' (s \\ t) = f '' s \\ f '' t`
can be understood through Level 7: injectivity lets image preserve
the intersection `s \\cap t^c`, and the key step connecting
`f '' t^c \\cap f '' s` to `(f '' t)^c \\cap f '' s` uses the same
witness collapse — if `y \\in f '' t^c` and `y \\in f '' t`, the
witnesses from `t^c` and `t` must be equal by injectivity, giving a
contradiction. The direct proof you wrote is cleaner for this
particular statement, but recognizing that set-difference results
DERIVE from intersection results via `s \\ t = s \\cap t^c` is an
important proof composition skill.

**The pattern**: Injectivity closes gaps because it eliminates the
possibility of different inputs producing the same output:

| Result | Without injectivity | With injectivity |
|---|---|---|
| Binary image of \\cap | only \\subseteq | = |
| Indexed image of \\bigcap | only \\subseteq | = |
| Image of \\\\ | only \\supseteq | = |
| Preimage-image roundtrip | only \\supseteq | = (next level!) |

The library name is `Set.image_diff`.
"

/-- `Set.image_diff` states that if `f` is injective, then
`f '' (s \\ t) = f '' s \\ f '' t`. Injective functions preserve
set difference as equality. -/
TheoremDoc Set.image_diff as "Set.image_diff" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Iff.rfl Set.image_diff
