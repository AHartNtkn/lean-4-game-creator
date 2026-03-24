import Game.Metadata

World "PsetImgPreimg"
Level 7

Title "Injectivity Closes the Intersection Gap"

TheoremTab "Set"

Introduction "
# Injectivity Restores Image ∩ Equality

In Image World, you proved `f '' (s \\cap t) \\subseteq f '' s \\cap f '' t` —
only a subset. Now prove the **reverse direction** under the hypothesis
that `f` is **injective**:

$$\\text{Injective}(f) \\;\\Longrightarrow\\; f(s) \\cap f(t) \\subseteq f(s \\cap t)$$

`Function.Injective f` means: if two inputs produce the same output,
the inputs must be equal:

$$\\forall\\, a_1\\, a_2,\\;\\; f(a_1) = f(a_2) \\;\\Longrightarrow\\; a_1 = a_2$$

In Lean, if `hinj : Function.Injective f` and `hab : f a = f b`, then
`hinj hab : a = b`.
"

/-- `Function.Injective f`, written `Function.Injective f`, means
that `f` maps distinct inputs to distinct outputs:

$$\\forall\\, a_1\\, a_2,\\;\\; f(a_1) = f(a_2) \\;\\Longrightarrow\\; a_1 = a_2$$

## Syntax
```
hinj : Function.Injective f
hinj hab : a = b      -- from hab : f a = f b
```

## When to use it
When you have `f a = f b` and need `a = b`. Apply the injectivity
hypothesis to the equation.

## Example
```
-- hinj : Function.Injective f, hab : f a = f b
have h := hinj hab    -- h : a = b
```

## Warning
Injectivity is about the FUNCTION, not a specific equation. You
need a hypothesis `Function.Injective f` in scope.
-/
DefinitionDoc Function.Injective as "Function.Injective"

NewDefinition Function.Injective

/-- Injectivity closes the intersection gap for images. -/
Statement (α β : Type) (f : α → β) (s t : Set α)
    (hinj : Function.Injective f) :
    f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  Hint "Destructure both image memberships. After `rfl` substitutes
  in one, the second gives an equation `f b = f a` — apply
  injectivity to collapse the two witnesses into one."
  Hint (hidden := true) "`rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩` then
  `have heq := hinj hab` then `rw [heq] at hb` then
  `exact ⟨a, ⟨ha, hb⟩, rfl⟩`."
  Branch
    intro y hy
    obtain ⟨⟨a, ha, rfl⟩, b, hb, hab⟩ := hy
    have heq := hinj hab
    rw [heq] at hb
    exact ⟨a, ⟨ha, hb⟩, rfl⟩
  rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
  have heq := hinj hab
  rw [heq] at hb
  exact ⟨a, ⟨ha, hb⟩, rfl⟩

Conclusion "
You proved that injectivity closes the intersection gap!

The proof had four key steps:
1. `rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩` — destructure both
   image memberships
2. `have heq := hinj hab` — apply injectivity to get `b = a`
3. `rw [heq] at hb` — rewrite to get `a \\in t`
4. `exact ⟨a, ⟨ha, hb⟩, rfl⟩` — build the image of the intersection

**The witness collapse pattern**: Steps 2 and 3 are the defining proof
move for injectivity in image/preimage proofs. You have two witnesses
(`a` and `b`) that map to the same output. Injectivity collapses them
into one (`a = b`), letting you combine their set memberships. Watch
for this pattern — you will use it in every remaining level.

**Why does injectivity help?** If `y \\in f '' s \\cap f '' t`, there
exist `a \\in s` and `b \\in t` with `f a = f b = y`. Without
injectivity, `a` and `b` might differ, so neither is in `s \\cap t`.
With injectivity, `f a = f b` forces `a = b`, so the single element
belongs to both `s` and `t`.

**Combined with `Set.image_inter_subset` from Image World**, you now have:

$$\\text{Injective}(f) \\;\\Longrightarrow\\; f(s \\cap t) = f(s) \\cap f(t)$$

The \\subseteq direction (Image World L08) was unconditional; the
\\supseteq direction (this level) required injectivity.

**The full biconditional**: This result is not just a sufficient
condition — injectivity is NECESSARY. If `f '' (s \\cap t) = f '' s \\cap f '' t`
for ALL `s, t`, then `f` must be injective. To see why: suppose
`f a = f b`. Take `s = \\{a\\}` and `t = \\{b\\}`. Then
`f '' s \\cap f '' t = \\{f a\\}` is nonempty, so by the equality
hypothesis `f '' (\\{a\\} \\cap \\{b\\})` is nonempty, which forces
`\\{a\\} \\cap \\{b\\}` to be nonempty, so `a = b`. In other words,
\"image preserves all binary intersections\" is a *characterization*
of injectivity, not just a consequence.

**Looking ahead**: You will study `Function.Injective` extensively
in Injective World, where you will prove injectivity for specific
functions, compose injections, and extract injectivity from
compositions.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Iff.rfl Set.image_inter Set.image_inter_on Set.InjOn.image_inter
