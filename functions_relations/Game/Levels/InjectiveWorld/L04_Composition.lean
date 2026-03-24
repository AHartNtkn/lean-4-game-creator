import Game.Metadata

World "InjectiveWorld"
Level 4

Title "Composition Preserves Injectivity"

TheoremTab "Function"

Introduction "
# Composing Injective Functions

If `f` and `g` are both injective, then their composition `g ∘ f` is
also injective. Intuitively: if neither `f` nor `g` collapses distinct
inputs, then doing `f` followed by `g` cannot collapse them either.

The proof uses the canonical shape, then applies both injectivity
hypotheses in sequence:

1. Assume `(g ∘ f) a = (g ∘ f) b`, i.e., `g (f a) = g (f b)`
2. Since `g` is injective: `f a = f b`
3. Since `f` is injective: `a = b`

In Lean, `apply hf` reduces the goal from `a = b` to `f a = f b`
(because `hf : Injective f` says `f a = f b → a = b`). Similarly
for `hg`.

**New proof move**: chain `apply` through two injectivity hypotheses.
"

/-- The composition of two injective functions is injective. -/
Statement {α β γ : Type} {g : β → γ} {f : α → β}
    (hg : Function.Injective g) (hf : Function.Injective f) :
    Function.Injective (g ∘ f) := by
  Hint "Start with the canonical shape: `intro a b hab`."
  intro a b hab
  Hint "The goal is `a = b`. You have:
  - `hf : Injective f` — if `f a = f b` then `a = b`
  - `hg : Injective g` — if `g x = g y` then `x = y`
  - `hab : g (f a) = g (f b)` (definitionally)

  Strategy: use `apply hf` to reduce the goal to `f a = f b`,
  then `apply hg` to reduce it to `g (f a) = g (f b)`, which is `hab`."
  Hint (hidden := true) "`apply hf` then `apply hg` then `exact hab`."
  apply hf
  Hint "The goal is now `f a = f b`. Use `apply hg` to reduce it to
  `g (f a) = g (f b)`."
  apply hg
  Hint "The goal is now `g (f a) = g (f b)`, which is exactly `hab`.
  Use `exact hab`."
  exact hab

Conclusion "
You proved that composition preserves injectivity!

The proof peels back the composition layer by layer:
```
intro a b hab   -- assume g (f a) = g (f b)
apply hf        -- suffices to show f a = f b
apply hg        -- suffices to show g (f a) = g (f b)
exact hab       -- which is our assumption
```

**The `apply` chain**: Each `apply` uses an injectivity hypothesis to
reduce the goal by one function layer. `apply hf` reduces `a = b` to
`f a = f b`. Then `apply hg` reduces `f a = f b` to `g (f a) = g (f b)`.
The chain mirrors the function composition: we peel off `f` first
(outermost goal), then `g`.

**Warning**: The order matters! `apply hf` before `apply hg`. Think of
it as: to show `a = b`, we need `f a = f b` (via `hf`), and for that
we need `g (f a) = g (f b)` (via `hg`). We work from the inside out:
the goal `a = b` is the innermost, and `hab` is the outermost.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Injective.comp
