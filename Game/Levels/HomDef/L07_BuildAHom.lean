import Game.Metadata

World "HomDef"
Level 7

Title "Building a Homomorphism"

Introduction
"
So far you've *used* homomorphism properties. Now you'll *construct*
a homomorphism from scratch.

To verify that a function is a homomorphism, you must prove it
preserves multiplication. The helper lemma `MonoidHom.mk_fun` lets
you do this interactively:

`MonoidHom.mk_fun f hf` takes a function `f : G → H` and a proof
`hf : ∀ a b, f (a * b) = f a * f b`, and returns a bundled
homomorphism `G →* H` wrapped in an existential.

In a commutative group, the squaring map `g ↦ g * g` is a
homomorphism. Build it.

Strategy:
1. `apply MonoidHom.mk_fun (fun g => g * g)` — provide the function
2. `intro a b` — introduce the multiplication-preserving obligation
3. Prove `(a * b) * (a * b) = a * a * (b * b)` using `mul_mul_mul_comm`
"

/-- `MonoidHom.mk_fun f hf` constructs a group homomorphism from
a function `f` and a proof `hf` that `f` preserves multiplication.

After `apply MonoidHom.mk_fun (fun g => ...)`, you get a single
goal: prove that the function preserves multiplication. -/
TheoremDoc MonoidHom.mk_fun as "MonoidHom.mk_fun" in "Hom"

NewTheorem MonoidHom.mk_fun

TheoremTab "Hom"

DisabledTactic group

Statement (G : Type*) [CommGroup G] :
    ∃ f : G →* G, ∀ g, f g = g * g := by
  Hint "Use `apply MonoidHom.mk_fun (fun g => g * g)` to provide the
  squaring function and set up the multiplication-preserving obligation."
  apply MonoidHom.mk_fun (fun g => g * g)
  Hint "Now prove that squaring preserves multiplication:
  `(a * b) * (a * b) = a * a * (b * b)`.

  First, `intro a b` to name the elements."
  intro a b
  Hint "The goal is `(a * b) * (a * b) = a * a * (b * b)`.
  This is the interchange law `mul_mul_mul_comm`.

  Try `exact mul_mul_mul_comm a b a b`."
  exact mul_mul_mul_comm a b a b

Conclusion
"
You constructed a homomorphism by:
1. Providing the function (`fun g => g * g`)
2. Proving it preserves multiplication (via `mul_mul_mul_comm`)

This is the **homomorphism verification** pattern: define the function,
then prove `map_mul`. Everything else (`map_one`, `map_inv`) is derived
automatically.

On paper: *\"Define `φ : G → G` by `φ(g) = g²`. Then
`φ(ab) = (ab)² = abab = a²b²` (by commutativity), so `φ` is a
homomorphism.\"*

Notice that commutativity was essential — in a non-commutative group,
`(ab)² = abab ≠ a²b²` in general.
"
