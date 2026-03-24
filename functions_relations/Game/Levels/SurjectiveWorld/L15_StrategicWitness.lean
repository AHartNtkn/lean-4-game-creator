import Game.Metadata

World "SurjectiveWorld"
Level 15

Title "Applying Surjectivity to a Constructed Element"

TheoremTab "Function"

Introduction "
# Strategic Witness Choice

In Levels 9 and 10, you applied surjectivity hypotheses to variables
that were directly in scope: `hg c` and `hgf c`. The element you fed
to the hypothesis was the variable you had just introduced.

But sometimes the right element to feed to surjectivity is not a
variable in your context — you must **construct** it from what you have.

**Your task**: Given `hgf : Surjective (g ∘ f)` and `b : β`, prove
`∃ a, g (f a) = g b`.

The key question: which element should you feed to `hgf`? Since `hgf`
takes elements of `γ` and returns preimages under `g ∘ f`, you need
a `γ`-element. Look at the goal: it involves `g b`, and `g b : γ`.

If you apply `hgf` to `g b`:

`obtain ⟨a, ha⟩ := hgf (g b)`

you get `ha : g (f a) = g b` — which is exactly the goal!

**This is the boss pattern**: In the next level, you will apply `hgf`
to `g b` in the same way, then use injectivity to finish. This level
isolates the first half of that argument.
"

/-- Given surjective g ∘ f, for any b there exists a with g (f a) = g b. -/
Statement {α β γ : Type} {g : β → γ} {f : α → β}
    (hgf : Function.Surjective (g ∘ f)) (b : β) :
    ∃ a, g (f a) = g b := by
  Hint "The strategic choice: which element of `γ` should you feed to
  `hgf`? The goal involves `g b`, and `g b : γ`. Apply surjectivity
  to `g b`:

  `obtain ⟨a, ha⟩ := hgf (g b)`"
  Hint (hidden := true) "`obtain ⟨a, ha⟩ := hgf (g b)`."
  obtain ⟨a, ha⟩ := hgf (g b)
  Hint "Now `ha : (g ∘ f) a = g b`, which is definitionally
  `g (f a) = g b`. The witness is `a`. Use `use a`."
  use a
  Hint "The goal is `g (f a) = g b`, which is exactly `ha`.
  Use `exact ha`."
  Hint (hidden := true) "`exact ha`."
  exact ha

Conclusion "
The critical move was choosing `g b` as the argument to `hgf`. You had
to **construct** the element `g b` from the parameter `b` and the
function `g`, rather than using a variable already in scope.

```
obtain ⟨a, ha⟩ := hgf (g b)   -- apply surjectivity to g b
use a                          -- witness
exact ha                       -- g (f a) = g b
```

**The general strategy — apply surjectivity to a constructed element**:
When your goal involves `P (f a)` or requires a preimage under a
composed function, look for a surjectivity hypothesis that produces
preimages, and feed it the element your goal needs. The pattern:

1. Identify what element of the codomain you need a preimage for
2. **Construct** that element from what you have (here: `g b` from `b` and `g`)
3. Apply the surjectivity hypothesis to it

This strategy appears beyond this world: in algebra (lifting through
quotient maps), topology (sections of bundles), and anywhere you need
to find preimages under composed maps.

**Boss preview**: In the boss, you will do exactly this — apply `hgf`
to `g b` — and then use injectivity to conclude `f a = b`. This level
practiced the first half of that argument.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp Function.Surjective.of_comp Function.Surjective.of_comp_left Function.RightInverse.surjective Function.HasRightInverse.surjective
