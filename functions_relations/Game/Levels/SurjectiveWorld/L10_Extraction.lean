import Game.Metadata

World "SurjectiveWorld"
Level 10

Title "Extracting Surjectivity from Composition"

TheoremTab "Function"

Introduction "
# If g ∘ f is Surjective, then g is Surjective

In Level 9, you proved that composing two surjective functions gives a
surjective composition. Now consider the partial converse: if `g ∘ f` is
surjective, what can you say about `g` and `f` individually?

**Claim**: `Surjective (g ∘ f) → Surjective g`.

The idea: for any `c : γ`, surjectivity of `g ∘ f` gives `a` with
`g (f a) = c`. Then `f a` is a preimage of `c` under `g`.

**The deep asymmetry with injectivity**: In Injective World, you proved
`Injective (g ∘ f) → Injective f` — the INNER function inherits
injectivity. Here, `Surjective (g ∘ f) → Surjective g` — the OUTER
function inherits surjectivity. The roles are swapped!

| Composition property | Implies |
|---|---|
| `Injective (g ∘ f)` | `Injective f` (inner) |
| `Surjective (g ∘ f)` | `Surjective g` (outer) |

This makes sense: the composition tests every input of `f` (so `f` must
be injective), but it only uses `f`'s outputs as inputs to `g` (so `g`
is tested on enough inputs to be surjective, but `f` might miss outputs).
"

/-- If the composition g ∘ f is surjective, then g is surjective. -/
Statement {α β γ : Type} {g : β → γ} {f : α → β}
    (hgf : Function.Surjective (g ∘ f)) : Function.Surjective g := by
  Hint "Start with `intro c` as always for a surjectivity proof."
  intro c
  Hint "You need `b : β` with `g b = c`. You have `hgf : Surjective (g ∘ f)`,
  which for any `c` gives `a` with `(g ∘ f) a = c`, i.e., `g (f a) = c`.

  Apply surjectivity: `obtain ⟨a, ha⟩ := hgf c`."
  obtain ⟨a, ha⟩ := hgf c
  Hint "Now `ha : (g ∘ f) a = c`, which is definitionally `g (f a) = c`.
  The witness for `g` being surjective at `c` is `f a`:
  `g (f a) = c` is exactly what we need.

  Use `use f a`."
  use f a
  Hint "The goal is `g (f a) = c`. The hypothesis `ha` has type
  `(g ∘ f) a = c`, which is definitionally the same thing.
  Use `exact ha`."
  exact ha

Conclusion "
You extracted surjectivity of `g` from surjectivity of `g ∘ f`!

```
intro c                     -- arbitrary output
obtain ⟨a, ha⟩ := hgf c    -- g (f a) = c
use f a                     -- witness: f a
exact ha                    -- g (f a) = c
```

**The key insight**: `hgf c` gives `a` with `g (f a) = c`. We do not need
`a` itself as a preimage under `g` — we need `f a`. The composition hands
us a preimage of `c` under `g` for free (it is `f a`).

**Why it is so short**: The proof is only 4 lines because the witness
(`f a`) comes directly from the composition hypothesis. We do not need to
build anything new — just relabel what we already have.

**The converse for `f` is FALSE**: `Surjective (g ∘ f)` does NOT imply
`Surjective f`. You will prove a concrete counterexample in Level 12
using functions you already know.
(Compare: `Injective (g ∘ f)` does NOT imply `Injective g`.)
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp Function.Surjective.of_comp
