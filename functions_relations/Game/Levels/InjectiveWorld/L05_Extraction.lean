import Game.Metadata

World "InjectiveWorld"
Level 5

Title "Extracting Injectivity from Composition"

TheoremTab "Function"

Introduction "
# If g ∘ f is Injective, then f is Injective

In Level 4, you proved that composing two injective functions gives an
injective composition. Now consider the partial converse: if `g ∘ f` is
injective, what can you say about `f` and `g` individually?

**Claim**: `Injective (g ∘ f) → Injective f`.

The idea: if `f a = f b`, then applying `g` to both sides gives
`g (f a) = g (f b)`, which means `(g ∘ f) a = (g ∘ f) b`. Since
`g ∘ f` is injective, this forces `a = b`.

**New proof move**: After `intro a b hab` and `apply hgf`, the goal
becomes `(g ∘ f) a = (g ∘ f) b`. Use `show g (f a) = g (f b)` to
make the composition explicit, then `rw [hab]` to close it.

**Note**: The converse for `g` is FALSE! `Injective (g ∘ f)` does NOT
imply `Injective g`. (Example: `f : Fin 1 → Fin 2` and `g : Fin 2 → Fin 1`
with `g` non-injective but `g ∘ f` trivially injective.)
"

/-- If the composition g ∘ f is injective, then f is injective. -/
Statement {α β γ : Type} {g : β → γ} {f : α → β}
    (hgf : Function.Injective (g ∘ f)) : Function.Injective f := by
  Hint "Start with `intro a b hab` as always."
  intro a b hab
  Hint "The goal is `a = b`. You have:
  - `hgf : Injective (g ∘ f)` — if `g (f a) = g (f b)` then `a = b`
  - `hab : f a = f b`

  Strategy: use `apply hgf` to reduce the goal to `(g ∘ f) a = (g ∘ f) b`.
  Then build this from `hab`."
  apply hgf
  Hint "The goal is `(g ∘ f) a = (g ∘ f) b`, which is definitionally
  `g (f a) = g (f b)`. Use `show g (f a) = g (f b)` to make this
  explicit, then `rw [hab]` to finish."
  Hint (hidden := true) "`show g (f a) = g (f b)` then `rw [hab]`.
  Alternative: `exact congrArg g hab` (applying `g` to both sides of `hab`)."
  Branch
    exact congrArg g hab
  show g (f a) = g (f b)
  Hint "`hab : f a = f b`. Rewriting `f a` to `f b` in the goal makes
  both sides identical. Use `rw [hab]`."
  rw [hab]

Conclusion "
You extracted injectivity of `f` from injectivity of `g ∘ f`!

```
intro a b hab     -- assume f a = f b
apply hgf         -- suffices: g (f a) = g (f b)
show g (f a) = g (f b)
rw [hab]          -- f a = f b makes both sides equal
```

**The argument in words**: If `f a = f b`, then `g (f a) = g (f b)`
(applying the same function to equal inputs gives equal outputs).
Since `g ∘ f` is injective, `g (f a) = g (f b)` forces `a = b`.

**`show` clarifies composition**: After `apply hgf`, the goal displays
as `(g ∘ f) a = (g ∘ f) b`. The `show` step rewrites this as
`g (f a) = g (f b)`, making it visible that `rw [hab]` applies.

**Alternative — `congrArg`**: The theorem `congrArg g hab` directly
produces `g (f a) = g (f b)` from `hab : f a = f b` — it says
\"applying the same function to equal inputs gives equal outputs.\"
This one-step alternative replaces the `show` + `rw` pair:
`exact congrArg g hab`. You will see `congrArg` used throughout the
course whenever you need to \"apply a function to both sides.\"

**Asymmetry**: `Injective (g ∘ f) → Injective f` is true, but
`Injective (g ∘ f) → Injective g` is false. The composition only
*tests* every input of `f` (since every `a` gets sent through
`f` then `g`), but it may not test every input of `g` (only those
in the range of `f` get tested).
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Injective.of_comp Function.Injective.comp
