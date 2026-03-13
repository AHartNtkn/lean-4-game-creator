import Game.Metadata

World "HomBasics"
Level 6

Title "Injective Means Trivial Kernel"

Introduction
"
A function is **injective** if distinct inputs produce distinct outputs:

`Function.Injective f` means `∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂`

In Lean, if `hf : Function.Injective f` and you have a proof
`hab : f a = f b`, then `hf hab` gives you `a = b`.

**Claim**: if `f` is injective and `x ∈ ker(f)`, then `x = 1`.

The idea: `x ∈ ker(f)` means `f(x) = 1 = f(1)`. Since `f` is
injective, `x = 1`.

Strategy:
1. Unfold `hx` with `rw [MonoidHom.mem_ker] at hx` to get `f x = 1`
2. Rewrite `1` as `f 1`: `rw [← map_one f] at hx` to get `f x = f 1`
3. Apply injectivity: `exact hf hx`
"

/-- `Function.Injective f` means `f` sends distinct inputs to distinct
outputs:

`∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`

If `hf : Function.Injective f` and `hab : f a = f b`, then
`hf hab : a = b`.

A group homomorphism is injective if and only if its kernel is
trivial (`ker f = ⊥`). -/
DefinitionDoc Function.Injective as "Function.Injective"

NewDefinition Function.Injective

TheoremTab "Hom"

/-- Disabled — you will prove this yourself in the boss level. -/
TheoremDoc MonoidHom.ker_eq_bot_iff as "MonoidHom.ker_eq_bot_iff" in "Hom"

DisabledTactic simp group
DisabledTheorem MonoidHom.ker_eq_bot_iff injective_iff_map_eq_one injective_iff_map_eq_one'

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (x : G) (hx : x ∈ f.ker) : x = 1 := by
  Hint "Unfold the kernel membership: `rw [MonoidHom.mem_ker] at {hx}`."
  rw [MonoidHom.mem_ker] at hx
  Hint "Now `{hx} : f x = 1`. To use injectivity, you need an equation
  of the form `f x = f y`. Rewrite the `1` as `f 1`:
  `rw [← map_one f] at {hx}`."
  rw [← map_one f] at hx
  Hint (hidden := true) "Now `{hx} : f x = f 1`. Apply injectivity:
  `exact hf {hx}`."
  exact hf hx

Conclusion
"
If `f` is injective, the only element in `ker(f)` is `1`.

The pattern:
1. `rw [MonoidHom.mem_ker] at hx` → `hx : f x = 1`
2. `rw [← map_one f] at hx` → `hx : f x = f 1`
3. `exact hf hx` → `x = 1` by injectivity

This is the **backward direction** of the boss theorem:
*injective → trivial kernel*.

On paper: *\"If `f(x) = 1 = f(1)` and `f` is injective, then `x = 1`.\"*
"
