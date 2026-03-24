import Game.Metadata

World "SurjectiveWorld"
Level 11

Title "Right Cancelation: The Algebraic Characterization"

TheoremTab "Function"

Introduction "
# Surjections are Right-Cancelable

You have seen surjectivity as \"every output is hit.\" There is an
equivalent algebraic characterization: surjective functions can be
**right-canceled** from equations.

**Claim**: If `f` is surjective and `g₁ ∘ f = g₂ ∘ f`, then `g₁ = g₂`.

Intuitively: if two functions agree on all outputs of `f`, and `f`
covers every element of the codomain, then the two functions must agree
everywhere.

**Proof strategy**:
1. Use `ext b` to prove the function equality pointwise
2. Use surjectivity to get `a` with `f a = b`
3. Rewrite `b` to `f a` in the goal
4. Use the hypothesis `g₁ ∘ f = g₂ ∘ f` to conclude

**Note on `ext` for functions**: You have used `ext` for set equality
(`ext x` reduces `s = t` to `x ∈ s ↔ x ∈ t`). The same tactic works
for function equality: `ext b` reduces `g₁ = g₂` to `g₁ b = g₂ b`.
"

/-- Surjective functions are right-cancelable:
if g₁ ∘ f = g₂ ∘ f and f is surjective, then g₁ = g₂. -/
Statement {α β γ : Type} {f : α → β} {g₁ g₂ : β → γ}
    (hf : Function.Surjective f) (heq : g₁ ∘ f = g₂ ∘ f) : g₁ = g₂ := by
  Hint "The goal is a function equality `g₁ = g₂`. Use `ext b` to reduce
  it to `g₁ b = g₂ b` for an arbitrary `b`."
  Hint (hidden := true) "`ext b`."
  ext b
  Hint "The goal is `g₁ b = g₂ b`. You know `g₁` and `g₂` agree on
  outputs of `f` (from `heq`). Since `f` is surjective, `b` IS an
  output of `f`.

  Use surjectivity to get a preimage:
  `obtain ⟨a, ha⟩ := hf b`"
  Hint (hidden := true) "`obtain ⟨a, ha⟩ := hf b`."
  obtain ⟨a, ha⟩ := hf b
  Hint "Now `ha : f a = b`. Rewrite `b` back to `f a` in the goal
  using `rw [← ha]`. This transforms `g₁ b = g₂ b` into
  `g₁ (f a) = g₂ (f a)`."
  Hint (hidden := true) "`rw [← ha]` then `show (g₁ ∘ f) a = (g₂ ∘ f) a`
  then `rw [heq]`."
  rw [← ha]
  Hint "The goal is `g₁ (f a) = g₂ (f a)`. This is the same as
  `(g₁ ∘ f) a = (g₂ ∘ f) a`. Use `show` to make the composition
  structure explicit, then `rw [heq]` to apply the hypothesis."
  show (g₁ ∘ f) a = (g₂ ∘ f) a
  Hint "Now `rw [heq]` replaces `g₁ ∘ f` with `g₂ ∘ f`, making both
  sides identical."
  rw [heq]

Conclusion "
You proved the **right cancelation property** of surjections!

```
ext b                              -- prove pointwise
obtain ⟨a, ha⟩ := hf b            -- f a = b
rw [← ha]                         -- goal: g₁ (f a) = g₂ (f a)
show (g₁ ∘ f) a = (g₂ ∘ f) a     -- reveal composition
rw [heq]                          -- apply g₁ ∘ f = g₂ ∘ f
```

**The algebraic perspective**: In category theory, a morphism that is
right-cancelable is called an **epimorphism**. You just proved that
surjections are epimorphisms in the category of sets. (The converse is
also true for sets, but not in all categories.)

**The dual statement**: In Injective World, the dual property holds:
injective functions are **left-cancelable**. If `f` is injective and
`f ∘ g₁ = f ∘ g₂`, then `g₁ = g₂`. Injective = monomorphism,
surjective = epimorphism.

| Property | Cancelation | Category theory |
|---|---|---|
| Injective | Left-cancelable: `f ∘ g₁ = f ∘ g₂ → g₁ = g₂` | Monomorphism |
| Surjective | Right-cancelable: `g₁ ∘ f = g₂ ∘ f → g₁ = g₂` | Epimorphism |

**Proof moves used**: `ext` for function equality (new!), surjectivity
to get a preimage, backward rewrite `rw [← ha]`, and `show` to reveal
composition structure.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp Function.Surjective.of_comp Function.Surjective.injective_comp_right
