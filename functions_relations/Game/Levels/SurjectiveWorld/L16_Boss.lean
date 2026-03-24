import Game.Metadata

World "SurjectiveWorld"
Level 16

Title "Boss: Injective Outer + Surjective Composition"

TheoremTab "Function"

Introduction "
# Boss: Integration Challenge

This boss combines surjectivity and injectivity into a single proof.

**Setup**: You have:
- `f : α → β` and `g : β → γ`
- `hgf : Surjective (g ∘ f)` — the composition hits every element of γ
- `hg : Injective g` — `g` never collapses distinct inputs

**Goal**: Prove `Surjective f`.

**Why this works intuitively**: Since `g ∘ f` is surjective, every
`c : γ` has a preimage under `g ∘ f`. In particular, for any `b : β`,
the element `g b : γ` has a preimage `a` with `g (f a) = g b`. Since
`g` is injective, `g (f a) = g b` forces `f a = b`. So `a` is a
preimage of `b` under `f`.

**Skills needed**:
- The canonical surjectivity shape: `intro b`, `use` (Levels 1, 4)
- `obtain` to extract witnesses (Levels 2, 9, 10)
- Applying injectivity to an equation (Injective World)
- Strategic choice of WHICH element to apply surjectivity to (Level 15)
"

/-- If g ∘ f is surjective and g is injective, then f is surjective. -/
Statement {α β γ : Type} {g : β → γ} {f : α → β}
    (hgf : Function.Surjective (g ∘ f)) (hg : Function.Injective g) :
    Function.Surjective f := by
  Hint "Start with `intro b` to take an arbitrary element of `β`."
  intro b
  Hint "You need `a : α` with `f a = b`. The surjectivity hypothesis
  `hgf` can give you a witness for any element of `γ`. But which
  element of `γ` should you feed it?

  **Key insight**: You want to end up with `f a = b`. If you apply
  `hgf` to `g b`, you get `a` with `g (f a) = g b`. Then `g`'s
  injectivity gives `f a = b` — exactly what you need."
  Hint (hidden := true) "Try `obtain ⟨a, ha⟩ := hgf (g b)`."
  obtain ⟨a, ha⟩ := hgf (g b)
  Hint "Now `ha : (g ∘ f) a = g b`, which is definitionally
  `g (f a) = g b`. The witness is `a`. Use `use a`."
  use a
  Hint "The goal is `f a = b`. You have:
  - `hg : Injective g` — if `g x = g y` then `x = y`
  - `ha : (g ∘ f) a = g b` — definitionally `g (f a) = g b`

  Since `g` is injective and `g (f a) = g b`, we get `f a = b`.
  Use `exact hg ha`."
  Hint (hidden := true) "`exact hg ha`.
  (Alternative: `apply hg` then `exact ha`.)"
  Branch
    apply hg
    Hint "The goal is now `g (f a) = g b`, which is exactly `ha`.
    Use `exact ha`."
    exact ha
  exact hg ha

Conclusion "
Congratulations — you completed **Surjective World**!

## What You Learned

**The canonical surjectivity proof**:
```
intro b         -- take an arbitrary output
use witness     -- provide a preimage
verify          -- show f witness = b
```

Every surjectivity proof starts with `intro b`. What follows depends on
where the witness comes from:
- **Arithmetic**: solve `f a = b` for `a`, verify with `omega`
- **Composition**: chain `obtain` to unwrap layers
- **Extraction**: reuse `f a` from `hgf c`
- **Right inverse**: the witness is `g b`

**Disproving surjectivity**: Assume surjectivity, apply it to an
unreachable output, extract the impossible witness, contradict.

**Composition rules** (now complete with Injective World):

| Hypothesis | Conclusion |
|---|---|
| `Surjective g`, `Surjective f` | `Surjective (g ∘ f)` |
| `Surjective (g ∘ f)` | `Surjective g` |
| `RightInverse g f` | `Surjective f` |
| `Surjective (g ∘ f)`, `Injective g` | `Surjective f` |
| `Surjective (g ∘ f)` | `Surjective f` — **FALSE** |

**The big picture — injection/surjection asymmetry**:

| Property | Composition preserves | Extraction from g ∘ f | Inverse type |
|---|---|---|---|
| Injective | Yes | f (inner) | Left inverse |
| Surjective | Yes | g (outer) | Right inverse |

This asymmetry — injection tests the inner factor, surjection tests the
outer factor — is one of the deepest patterns in function theory.

**Looking ahead — quotient maps**: In QuotientLiftWorld, you will see that
the canonical projection from a type to a quotient type is always surjective.
The right-inverse / section machinery you learned here applies directly:
a section of a quotient map picks one representative from each equivalence
class.

**Next: Bijective World**. A function is bijective when it is both
injective and surjective. You will prove `Bijective f` by splitting into
`Injective f ∧ Surjective f` and reusing the proof shapes from both
worlds — the `intro a b hab` shape for injectivity and the `intro b; use`
shape for surjectivity, combined in a single proof.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp Function.Surjective.of_comp Function.Surjective.of_comp_left Function.RightInverse.surjective Function.HasRightInverse.surjective
