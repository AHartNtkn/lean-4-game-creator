import Game.Metadata

World "HomDef"
Level 3

Title "Group Homomorphisms"

Introduction
"
A **group homomorphism** is a function between groups that preserves
multiplication. In Lean 4 + Mathlib, group homomorphisms use the type
`MonoidHom` with notation `G →* H`.

⚠️ The notation is `→*` (with a star), not `→` (plain function arrow).
The name `MonoidHom` is used because the definition works for monoids
too — but it applies equally to groups.

The defining property is `map_mul`:

`map_mul f a b : f (a * b) = f a * f b`

Given `f : G →* H`, the lemma `map_mul f a b` tells you that `f`
distributes over multiplication.

Prove that `f (a * b) = f a * f b` using `map_mul`.
"

/-- A group homomorphism from `G` to `H`. A function `f : G →* H`
satisfying `f (a * b) = f a * f b` for all `a, b : G`.

In Lean, the notation is `→*` (not `→`). The type name is `MonoidHom`
because the definition works for any `MulOneClass`, but it applies to
groups. -/
DefinitionDoc MonoidHom as "MonoidHom (→*)"

NewDefinition MonoidHom

/-- `map_mul` says: for any group homomorphism `f : G →* H`,

`f (a * b) = f a * f b`

This is the defining property of a group homomorphism. Everything
else — `map_one` and `map_inv` — follows from this single axiom.

Use `exact map_mul f a b` to close a goal of this form, or
`rw [map_mul]` to rewrite `f (a * b)` to `f a * f b`. -/
TheoremDoc map_mul as "map_mul" in "Hom"

NewTheorem map_mul

TheoremTab "Hom"

DisabledTactic group simp

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b : G) :
    f (a * b) = f a * f b := by
  Hint "The lemma `map_mul f a b` states exactly this. Try
  `exact map_mul f a b`."
  Hint (hidden := true) "Or use `rw [map_mul]` to rewrite the left side,
  which will close the goal by `rfl`."
  Branch
    rw [map_mul]
  exact map_mul f a b

Conclusion
"
You've used `map_mul` — the defining property of a group homomorphism.

Whenever you see `f (a * b)` where `f : G →* H`, you can rewrite it
to `f a * f b` using `map_mul`.

For a concrete example: if both groups are the integers under addition,
then `f(n) = 2n` is a homomorphism because `2(a + b) = 2a + 2b`. The
`map_mul` property is just the statement that `f` distributes over the
group operation.

A natural question: does `f` also preserve the identity and inverses?
That is, does `f 1 = 1` and `f a⁻¹ = (f a)⁻¹`? The answer is **yes**,
and remarkably, both facts are *consequences* of `map_mul` alone.
You'll derive `map_one` yourself in the next level.
"
