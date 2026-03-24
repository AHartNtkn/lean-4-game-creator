import Game.Metadata

World "PreimageWorld"
Level 14

Title "Preimage Reverses Composition"

TheoremTab "Set"

Introduction "
# The Deepest Fact About Preimages

You have proved that preimage preserves intersection, union,
complement, indexed unions, indexed intersections, and more. But
WHY does preimage preserve everything?

The answer is one equation:

$$(g \\circ f)^{-1}(t) = f^{-1}(g^{-1}(t))$$

Preimage **reverses** function composition. If you compose `g` after
`f`, then the preimage of `t` is obtained by first taking the
preimage under `g`, then taking the preimage under `f`.

This means preimage is just **composition on the predicate level**.
Since composition preserves all logical structure, preimage preserves
all set operations. That single fact explains every result in this
world.

Notice the order reversal: `g . f` applies `f` first, then `g`. But
the preimage pulls back through `g` first, then `f`. This is
called **contravariance** — preimage reverses the direction of
composition.

**Proof plan**:
1. `ext x` then `constructor`
2. Both directions: `intro hx; exact hx` — the two sides are
   definitionally equal (both reduce to `g (f x) ∈ t`)
"

/-- `Set.preimage_comp` states that preimage reverses composition:
`(g . f) ⁻¹' s = f ⁻¹' (g ⁻¹' s)`.

## When to use it
When you need to simplify a preimage under a composed function
into nested preimages.

## Example
If `f : α → β` and `g : β → γ` and `t : Set γ`, then
`(g . f) ⁻¹' t = f ⁻¹' (g ⁻¹' t)`.
-/
TheoremDoc Set.preimage_comp as "Set.preimage_comp" in "Set"

/-- Preimage reverses function composition. -/
Statement (α β γ : Type) (f : α → β) (g : β → γ) (t : Set γ) :
    (g ∘ f) ⁻¹' t = f ⁻¹' (g ⁻¹' t) := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  · Hint "**Forward**: Both sides reduce to `g (f x) ∈ t`.
    The left side `x ∈ (g . f) ⁻¹' t` means `(g . f) x ∈ t`,
    which is `g (f x) ∈ t`. The right side `x ∈ f ⁻¹' (g ⁻¹' t)`
    means `f x ∈ g ⁻¹' t`, which is `g (f x) ∈ t`. Same thing."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx
  · Hint "**Backward**: same reasoning — both sides reduce to
    `g (f x) ∈ t`."
    Hint (hidden := true) "`intro hx` then `exact hx`."
    intro hx
    exact hx

Conclusion "
You proved that preimage reverses composition — both directions were
`intro hx; exact hx` because the two sides are definitionally equal:
both say `g (f x) ∈ t`.

This trivial proof carries a deep message: **preimage is a
contravariant functor**. It maps sets of outputs to sets of inputs,
and it reverses the order of function composition. Every preservation
result you proved in this world — for `∩`, `∪`, `ᶜ`, `⋃`, `⋂`,
`\\` — follows from this single structural fact.

**The deepest way to see it**: Since `Set α = α → Prop`, a set IS a
predicate. Preimage is just composition: `x ∈ f ⁻¹' t` is the same
as `(t . f) x`. Every preservation result in this world reduces to
the fact that logical connectives (`∧`, `∨`, `¬`, `∀`, `∃`)
distribute over function composition. Preimage preserves everything
because composition preserves everything.

The library name is `Set.preimage_comp`.

**Foreshadowing**: In the Injective and Surjective Worlds, you will
prove facts like 'if `g . f` is injective then `f` is injective.'
The composition-reversal pattern you see here will appear again
in those proofs — reasoning about `g . f` requires peeling apart
the composition, just as preimage does.

**Preimage and injectivity**: You proved that preimage preserves
every set operation. But there is one thing preimage does NOT
guarantee: `f ⁻¹' (f '' s) = s`. The inclusion `s ⊆ f ⁻¹' (f '' s)`
always holds (if `x ∈ s` then `f x ∈ f '' s` so `x ∈ f ⁻¹' (f '' s)`),
but the reverse can fail. If `f` maps two different inputs to the
same output, then `f ⁻¹' (f '' s)` can be strictly larger than `s`.
Equality `f ⁻¹' (f '' s) = s` for all `s` is equivalent to `f` being
**injective** — that is exactly what Injective World will explore.
"

NewTheorem Set.preimage_comp

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_comp Iff.rfl
