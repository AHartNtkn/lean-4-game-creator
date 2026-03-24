import Game.Metadata

World "SurjectiveWorld"
Level 14

Title "Constructing a Right Inverse"

TheoremTab "Function"

Introduction "
# Surjective Implies Right Inverse (via Choice)

In Level 13, you proved the easy direction: if `f` has a right inverse,
then `f` is surjective. Now prove the converse: if `f` is surjective,
then `f` has a right inverse.

**The Axiom of Choice in action**: If `f` is surjective, then for every
`b : β` there exists some `a` with `f a = b`. To build a right inverse
`g : β → α`, we need to *choose* one such `a` for every `b`
simultaneously. This is exactly what the Axiom of Choice does.

In Lean 4, Choice is built into the logic via `Exists.choose` and
`Exists.choose_spec`:

- `Exists.choose` : given `h : ∃ x, P x`, produces a witness `x`
- `Exists.choose_spec` : given `h : ∃ x, P x`, proves `P (h.choose)`

So if `hf : Surjective f`, then `hf b : ∃ a, f a = b`, and:
- `(hf b).choose : α` — a chosen preimage of `b`
- `(hf b).choose_spec : f ((hf b).choose) = b` — proof it works

**Your task**: Construct a right inverse for a surjective function.
Use `fun b => (hf b).choose` as the right inverse function, then
verify it works using `choose_spec`.
"

/-- `Function.HasRightInverse f` means that `f` has a right inverse:
there exists a function `g` such that `f (g x) = x` for all `x`.

$$\text{HasRightInverse}(f) \;\;\equiv\;\; \exists\, g,\;\; \text{RightInverse}(g, f)$$

## Syntax
```
h : Function.HasRightInverse f
obtain ⟨g, hg⟩ := h    -- g : β → α, hg : RightInverse g f
```

## When to use it
When the goal is `HasRightInverse f`, you need to provide a function `g`
and prove that `g` is a right inverse of `f`. Use `use g` to provide the
function, then prove `RightInverse g f`.

## Connection to surjectivity
A function has a right inverse if and only if it is surjective (the
backward direction uses the Axiom of Choice).
-/
DefinitionDoc Function.HasRightInverse as "Function.HasRightInverse"

/-- `Exists.choose` extracts a witness from an existential proof using
the Axiom of Choice.

Given `h : ∃ x, P x`, the term `h.choose` has type `α` — it is a
concrete element satisfying the existential.

## Syntax
```
h.choose           -- dot notation
Exists.choose h    -- full name
```

## When to use it
When you need to BUILD A FUNCTION from existential hypotheses.
Unlike `obtain` (which works in tactic mode and introduces a local
variable), `choose` works in term mode and can appear inside lambda
expressions:
```
fun b => (hf b).choose    -- a function built from Choice
```

## Companion
Always pair with `Exists.choose_spec` to prove the witness satisfies
the predicate: `h.choose_spec : P (h.choose)`.
-/
DefinitionDoc Exists.choose as "Exists.choose"

/-- `Exists.choose_spec` proves that the witness extracted by
`Exists.choose` satisfies the existential predicate.

Given `h : ∃ x, P x`, the term `h.choose_spec` has type `P (h.choose)`.

## Syntax
```
h.choose_spec           -- dot notation
Exists.choose_spec h    -- full name
```

## Example
```
-- hf : Surjective f, b : β
-- (hf b).choose : α
-- (hf b).choose_spec : f ((hf b).choose) = b
```
-/
TheoremDoc Exists.choose_spec as "Exists.choose_spec" in "Logic"

/-- Every surjective function has a right inverse. -/
Statement {α β : Type} {f : α → β}
    (hf : Function.Surjective f) : Function.HasRightInverse f := by
  Hint "The goal is `HasRightInverse f`, which is `∃ g, RightInverse g f`,
  i.e., `∃ g, ∀ b, f (g b) = b`. You need to provide a function `g`
  and prove it is a right inverse.

  Use `use fun b => (hf b).choose` to provide the right inverse."
  Hint (hidden := true) "`use fun b => (hf b).choose`."
  use fun b => (hf b).choose
  Hint "Now prove `Function.RightInverse (fun b => (hf b).choose) f`,
  i.e., `∀ b, f ((hf b).choose) = b`.

  Start with `intro b`."
  intro b
  Hint "The goal is `f ((hf b).choose) = b`. This is exactly what
  `Exists.choose_spec` gives you: `(hf b).choose_spec` proves
  `f ((hf b).choose) = b`.

  Use `exact (hf b).choose_spec`."
  Hint (hidden := true) "`exact (hf b).choose_spec`."
  exact (hf b).choose_spec

Conclusion "
You constructed a right inverse from surjectivity using the Axiom of Choice!

```
use fun b => (hf b).choose    -- the right inverse function
intro b                        -- take arbitrary b
exact (hf b).choose_spec       -- f (chosen preimage) = b
```

**What just happened**: For each `b`, surjectivity gives `∃ a, f a = b`.
`Exists.choose` picks one such `a`, and `Exists.choose_spec` proves
it satisfies `f a = b`. Packaging all these choices into a function
`g b = (hf b).choose` gives the right inverse.

**The Choice mechanism in Lean 4**:
- `h.choose` : extracts a witness from `h : ∃ x, P x`
- `h.choose_spec` : proves `P (h.choose)`

Unlike `obtain`, which destructures an existential in tactic mode,
`choose`/`choose_spec` work in term mode and can be used inside
lambda expressions to build functions.

**The full picture** (Level 13 + this level):

| Direction | Statement | Needs Choice? |
|---|---|---|
| → (Level 13) | `RightInverse g f → Surjective f` | No |
| ← (this level) | `Surjective f → HasRightInverse f` | Yes |

The forward direction is constructive — given `g`, the witness `g b`
is explicit. The backward direction requires choosing preimages, which
is fundamentally non-constructive.

**About `Function.HasRightInverse`**: The conclusion type of this level,
`HasRightInverse f`, wraps the right inverse in an existential:
`∃ g, RightInverse g f`. This definition will become important in
Bijective World, where the existence of both a left and right inverse
characterizes bijectivity. For now, the key concept is the Choice
mechanism (`Exists.choose` / `choose_spec`) that makes the construction
possible.
"

NewDefinition Exists.choose
NewTheorem Exists.choose_spec

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.RightInverse.surjective Function.HasRightInverse.surjective Function.Surjective.comp Function.Surjective.hasRightInverse
