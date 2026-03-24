import Game.Metadata

World "PsetImgPreimg"
Level 8

Title "Injectivity Closes the Indexed Intersection Gap"

TheoremTab "Set"

NewDefinition Nonempty

Introduction "
# Indexed Intersection Under Injectivity

In Level 4, you proved `f '' (\\bigcap_i s_i) \\subseteq \\bigcap_i f '' (s_i)` —
only a subset. The reverse direction failed because different indices
might use different witnesses that cannot be unified into one element
of the full intersection.

In Level 7, you used the **witness collapse** pattern to close the
gap for binary intersection. Now do the same for the **indexed** case:

$$\\text{Injective}(f) \\;\\Longrightarrow\\;
\\bigcap_i f(s_i) \\subseteq f\\left(\\bigcap_i s_i\\right)$$

The strategy is an indexed version of Level 7's witness collapse.
For each index `i`, you get a witness `a_i \\in s_i` with
`f(a_i) = y`. Injectivity forces all these witnesses to be the same
element, which therefore belongs to every `s_i`.

**New prerequisite — `Nonempty`**: This level needs the index type
`ι` to have at least one element, written `[Nonempty ι]` in the
function signature. This is a **typeclass**: Lean finds the instance
automatically. To use it in a proof, write:

```
obtain ⟨i₀⟩ := ‹Nonempty ι›
```

The French quotes `‹...›` mean \"retrieve the typeclass instance from
context.\" After this line, `i₀ : ι` is a concrete index you can use.

Note: `Nonempty ι` (a TYPE has elements) is different from
`Set.Nonempty s` (a SET has elements). `Nonempty` is about the type
itself.
"

/-- Injectivity closes the indexed intersection gap for images. -/
Statement (α β ι : Type) [Nonempty ι] (f : α → β) (s : ι → Set α)
    (hinj : Function.Injective f) :
    ⋂ i, f '' (s i) ⊆ f '' (⋂ i, s i) := by
  Hint "Convert the indexed intersection hypothesis to `\\forall i`,
  extract a starting index with `obtain ⟨i₀⟩ := ‹Nonempty ι›`, get
  a concrete witness, then use the witness collapse pattern for each
  remaining index."
  Hint (hidden := true) "`intro y hy` then `rw [Set.mem_iInter] at hy`
  then `obtain ⟨i₀⟩ := ‹Nonempty ι›` then
  `obtain ⟨x, hx₀, rfl⟩ := hy i₀` then `use x` then `constructor`
  then `rw [Set.mem_iInter]` then `intro i` then
  `obtain ⟨a, ha, hfa⟩ := hy i` then `have heq := hinj hfa` then
  `rw [heq] at ha` then `exact ha` then `rfl`."
  intro y hy
  rw [Set.mem_iInter] at hy
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨x, hx₀, rfl⟩ := hy i₀
  use x
  constructor
  · rw [Set.mem_iInter]
    intro i
    obtain ⟨a, ha, hfa⟩ := hy i
    have heq := hinj hfa
    rw [heq] at ha
    exact ha
  · rfl

Conclusion "
You proved the indexed version of Level 7's result: injectivity
closes the indexed intersection gap.

The proof used the **witness collapse** pattern once per index.
For each `i`, you extracted a witness `a \\in s_i` with `f a = f x`,
then injectivity gave `a = x`, so `x \\in s_i`. Since this works for
every `i`, `x \\in \\bigcap_i s_i`.

**Combined with `Set.image_iInter_subset` from Level 4**, you now have:

$$\\text{Injective}(f) \\;\\Longrightarrow\\;
f\\left(\\bigcap_i s_i\\right) = \\bigcap_i f(s_i)$$

The \\subseteq direction (Level 4) was unconditional; the \\supseteq
direction (this level) required injectivity.

The library name is `Set.InjOn.image_iInter_eq` (stated for the
weaker `Set.InjOn` hypothesis — you will meet `InjOn` in
MapsToInjOnWorld).
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Iff.rfl Set.InjOn.image_iInter_eq Set.image_iInter Set.image_iInter_subset
