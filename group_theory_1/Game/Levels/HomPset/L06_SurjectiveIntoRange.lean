import Game.Metadata

World "HomPset"
Level 6

Title "Surjectivity and the Range"

Introduction
"
A function is **surjective** if every element in the target is hit:

`Function.Surjective f` means `∀ y, ∃ x, f x = y`

This is the dual of injectivity. You already proved that
`f` is injective iff `ker(f) = ⊥` (kernel is trivial).
The dual statement is: `f` is surjective iff `range(f) = ⊤`
(range is everything). You'll prove that equivalence in the boss.

For now: given that `f` is surjective, show that every element
of `H` is in the range. Unpack the definitions.
"

/-- `Function.Surjective f` means `f` hits every element of the
target:

`∀ (b : H), ∃ (a : G), f a = b`

If `hs : Function.Surjective f` and `y : H`, then `hs y`
gives `∃ x, f x = y`.

A group homomorphism is surjective if and only if its range
is the whole group (`f.range = ⊤`). -/
DefinitionDoc Function.Surjective as "Function.Surjective"

NewDefinition Function.Surjective

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (hs : Function.Surjective f) (y : H) : y ∈ f.range := by
  Hint "Unfold range membership: `rw [MonoidHom.mem_range]`."
  rw [MonoidHom.mem_range]
  Hint "`Function.Surjective f` means `∀ y, ∃ x, f x = y`.
  Since `{hs} : Function.Surjective f`, you can apply it to `y`:
  `exact {hs} y`."
  Branch
    -- Alternative: use specialize to pin the universal
    Hint "You used `specialize` to pin `{hs}` to `y`. Now `{hs}`
    gives the exact existential you need: `exact {hs}`."
    specialize hs y
    exact hs
  exact hs y

Conclusion
"
If `f` is surjective, then every element of `H` is in `f.range`.

The argument is immediate from the definitions: `Function.Surjective f`
says `∀ y, ∃ x, f x = y`, and `y ∈ f.range` means `∃ x, f x = y`.
They're the same statement.

This means `f.range = ⊤` (the range is the whole group). Conversely,
if `f.range = ⊤`, then every `y ∈ H` is in the range, which means
`f` is surjective. You'll prove this biconditional in the boss.

The dual picture:

| Property | Definition | Subgroup condition |
|----------|------------|--------------------|
| Injective | `f a = f b → a = b` | `ker(f) = ⊥` |
| Surjective | `∀ y, ∃ x, f x = y` | `range(f) = ⊤` |
"
