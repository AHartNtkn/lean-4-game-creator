import Game.Metadata

World "SurjectiveWorld"
Level 9

Title "Composition Preserves Surjectivity"

TheoremTab "Function"

Introduction "
# Composing Surjective Functions

If `f` and `g` are both surjective, then their composition `g ∘ f` is
also surjective. Intuitively: if both `f` and `g` cover their codomains,
then doing `f` followed by `g` covers the final codomain too.

The proof **chains witnesses** — the dual of chaining `apply` for injectivity:

1. Given `c : γ`, use `g`'s surjectivity to find `b` with `g b = c`
2. Use `f`'s surjectivity to find `a` with `f a = b`
3. Then `a` is the witness: `g (f a) = g b = c`

**Compare with Injective World**: Injectivity composition
used an `apply` chain (peeling layers off). Surjectivity composition
uses an `obtain` chain (building layers up).
"

/-- The composition of two surjective functions is surjective. -/
Statement {α β γ : Type} {g : β → γ} {f : α → β}
    (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Surjective (g ∘ f) := by
  Hint "Start with `intro c` to get an arbitrary element of the codomain."
  intro c
  Hint "You need a witness `a` with `(g ∘ f) a = c`, i.e., `g (f a) = c`.
  Strategy: first find `b` with `g b = c` (from `hg`), then find `a`
  with `f a = b` (from `hf`).

  Use `obtain ⟨b, hb⟩ := hg c`."
  obtain ⟨b, hb⟩ := hg c
  Hint "Now `hb : g b = c`. You need `a` with `f a = b`.
  Use `obtain ⟨a, ha⟩ := hf b`."
  obtain ⟨a, ha⟩ := hf b
  Hint "Now `ha : f a = b` and `hb : g b = c`. The witness is `a`:
  `g (f a) = g b = c`. Use `use a`."
  use a
  Hint "The goal is `(g ∘ f) a = c`, which is definitionally `g (f a) = c`.
  Use `show g (f a) = c` to make the structure explicit, then
  `rw [ha]` to replace `f a` with `b`."
  Hint (hidden := true) "`show g (f a) = c` then `rw [ha]` then `exact hb`."
  show g (f a) = c
  Hint "`ha : f a = b`. Rewriting replaces `f a` with `b` in the goal,
  giving `g b = c`. Use `rw [ha]`."
  rw [ha]
  Hint "The goal is now `g b = c`, which is exactly `hb`. Use `exact hb`."
  exact hb

Conclusion "
You proved that composition preserves surjectivity!

```
intro c                       -- arbitrary output
obtain ⟨b, hb⟩ := hg c       -- g b = c
obtain ⟨a, ha⟩ := hf b       -- f a = b
use a                         -- witness for g ∘ f
show g (f a) = c
rw [ha]                       -- g (f a) = g b
exact hb                      -- g b = c
```

**The `obtain` chain**: Each `obtain` peels back one function layer.
First we find a preimage under `g`, then a preimage under `f`. The chain
mirrors the function composition: we unwrap `g` first (outermost), then `f`.

**Dual comparison**:

| Injectivity (apply chain) | Surjectivity (obtain chain) |
|---|---|
| `apply hf; apply hg; exact hab` | `obtain from hg; obtain from hf; use a` |
| Peels layers from inside out | Builds witnesses from outside in |
| Works backward from goal | Works forward from hypotheses |

**Witness transfer**: The pattern of obtaining a witness from one
surjectivity hypothesis and transforming it into the witness you need
is called **witness transfer**. Here you transferred `b` (from `hg`)
into `a` (via `hf`). You will use this pattern throughout the rest of
this world.

**The `show` step**: After `use a`, the goal displays as `(g ∘ f) a = c`.
Writing `show g (f a) = c` reveals the composition structure so that
`rw [ha]` can find `f a` to replace.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp
