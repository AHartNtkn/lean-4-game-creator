import Game.Metadata

World "InjectiveWorld"
Level 7

Title "Left Inverses Imply Injectivity"

TheoremTab "Function"

Introduction "
# Left Inverses

A function `g : β → α` is a **left inverse** of `f : α → β` if
`g ∘ f = id`, meaning `g (f x) = x` for every `x`.

In Lean, this is `Function.LeftInverse g f`:

$$\\text{LeftInverse}(g, f) \\;\\;:\\equiv\\;\\; \\forall\\, x,\\;\\; g(f(x)) = x$$

**Key theorem**: If `f` has a left inverse, then `f` is injective.

The idea: If `f a = f b`, apply `g` to both sides to get
`g (f a) = g (f b)`. Since `g` is a left inverse: `g (f a) = a` and
`g (f b) = b`. So `a = g (f a) = g (f b) = b`.

**Proof plan** (using the rewriting moves from Level 6):
1. `intro a b hab` — canonical injectivity start
2. `have ha := h a` — get `g (f a) = a`
3. `have hb := h b` — get `g (f b) = b`
4. `rw [hab] at ha` — update `ha` to `g (f b) = a`
5. `rw [← ha, hb]` — chain equalities to conclude `a = b`
"

/-- `Function.LeftInverse g f` means that `g` undoes `f`:
`g (f x) = x` for every `x`. Equivalently, `g ∘ f = id`.

## Syntax
```
h : Function.LeftInverse g f
h x : g (f x) = x           -- apply to a specific element
```

## When to use it
When you need to cancel `f` using a retraction `g`. If `h` is a
proof of `LeftInverse g f` and you have `f a` somewhere, applying
`h a` gives you `g (f a) = a`.

## Example
```
-- h : Function.LeftInverse g f
have ha := h a    -- ha : g (f a) = a
```

## Connection to injectivity
If `f` has a left inverse, then `f` is injective: from `f a = f b`,
apply `g` to get `a = g (f a) = g (f b) = b`.

## Warning
`LeftInverse g f` means `g` is the left inverse of `f`, not that
`f` is the left inverse of `g`. The order matters:
- `LeftInverse g f` means `g ∘ f = id` (g cancels f)
- `LeftInverse f g` means `f ∘ g = id` (f cancels g)
-/
DefinitionDoc Function.LeftInverse as "Function.LeftInverse"

/-- If f has a left inverse g, then f is injective. -/
Statement {α β : Type} {g : β → α} {f : α → β}
    (h : Function.LeftInverse g f) : Function.Injective f := by
  Hint "Start with `intro a b hab` as always."
  intro a b hab
  Hint "You have:
  - `h : LeftInverse g f` — meaning `g (f x) = x` for all `x`
  - `hab : f a = f b`

  Strategy: extract `g (f a) = a` and `g (f b) = b` from `h`,
  then use `hab` to connect them.

  Try `have ha := h a` and `have hb := h b`."
  Hint (hidden := true) "`have ha := h a` then `have hb := h b` then
  `rw [hab] at ha` then `rw [← ha, hb]`."
  have ha := h a
  have hb := h b
  Hint "Now you have:
  - `ha : g (f a) = a`
  - `hb : g (f b) = b`
  - `hab : f a = f b`

  From `hab`, rewriting in `ha` gives `g (f b) = a`. Combined with
  `hb : g (f b) = b`, you get `a = b`.

  Use `rw [hab] at ha` to update `ha`."
  rw [hab] at ha
  Hint "Now `ha : g (f b) = a` and `hb : g (f b) = b`. Since both
  equal `g (f b)`, we have `a = b`.

  Use `rw [← ha, hb]`: first `← ha` rewrites `a` to `g (f b)` in the
  goal, then `hb` rewrites `g (f b)` to `b`."
  Hint (hidden := true) "`rw [← ha, hb]`"
  Branch
    rw [← ha]
    exact hb
  rw [← ha, hb]

Conclusion "
You proved that left inverses imply injectivity!

```
intro a b hab
have ha := h a        -- g (f a) = a
have hb := h b        -- g (f b) = b
rw [hab] at ha        -- g (f b) = a
rw [← ha, hb]        -- a = g (f b) = b
```

**The chain of equalities**: The proof establishes
`a = g (f a) = g (f b) = b`, where:
- The first `=` comes from `ha` (left inverse property)
- The middle `=` comes from `hab` (the injectivity assumption `f a = f b`)
- The last `=` comes from `hb` (left inverse property again)

**Why left inverses force injectivity**: A left inverse `g` \"remembers\"
the original input. Since `g (f x) = x` always recovers `x`, no
information can be lost by applying `f`. If two inputs gave the
same output, `g` could not recover both — contradiction.

**Looking ahead**: The boss will ask you to combine left-inverse
reasoning with injectivity and `apply` — integrating techniques from
across this world.
"

NewDefinition Function.LeftInverse

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.LeftInverse.injective Function.HasLeftInverse.injective Function.Injective.comp Function.Injective.of_comp
