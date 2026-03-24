import Game.Metadata

World "InjectiveWorld"
Level 8

Title "Boss: Left Inverse Meets Composition"

TheoremTab "Function"

Introduction "
# Boss: Integration Challenge

This boss combines techniques from across Injective World into a single
proof:

- The canonical `intro a b hab` shape (Levels 1–2)
- Extracting an explicit equation with `have` (Levels 1–2)
- Left-inverse instantiation: `have ha := hinv (f a)` (Level 7)
- Rewriting at hypotheses: `rw [...] at` (Levels 6–7)
- Applying injectivity via `apply` (Levels 4–5)
- Backward rewriting: `rw [← ...]` (Levels 6–7)

**Setup**: You have a function `f : α → β` that is injective, a function
`g : β → γ` that has a left inverse `r` (meaning `r (g x) = x` for all
`x`), and you must prove that the composition `g ∘ f` is injective.

**Strategy**: If `g (f a) = g (f b)`, apply `r` to both sides using the
left-inverse property to recover `f a` and `f b`. Then use `f`'s
injectivity to conclude `a = b`.
"

/-- If g has a left inverse and f is injective, then g ∘ f is injective. -/
Statement {α β γ : Type} {g : β → γ} {r : γ → β} {f : α → β}
    (hinv : Function.LeftInverse r g) (hf : Function.Injective f) :
    Function.Injective (g ∘ f) := by
  Hint "Start with the canonical injectivity shape: `intro a b hab`."
  intro a b hab
  Hint "The hypothesis `hab` has type `(g ∘ f) a = (g ∘ f) b`, which is
  definitionally `g (f a) = g (f b)`. Extract the explicit equation:
  `have hab' : g (f a) = g (f b) := hab`"
  Hint (hidden := true) "`have hab' : g (f a) = g (f b) := hab`"
  have hab' : g (f a) = g (f b) := hab
  Hint "Now use the left inverse to recover `f a` and `f b`. Since
  `hinv : LeftInverse r g` means `r (g x) = x` for all `x`, apply it
  to `f a` and `f b`:
  `have ha := hinv (f a)` and `have hb := hinv (f b)`."
  Hint (hidden := true) "`have ha := hinv (f a)` then `have hb := hinv (f b)`."
  have ha := hinv (f a)
  have hb := hinv (f b)
  Hint "You now have:
  - `ha : r (g (f a)) = f a`
  - `hb : r (g (f b)) = f b`
  - `hab' : g (f a) = g (f b)`

  Use `rw [hab'] at ha` to replace `g (f a)` with `g (f b)` in `ha`."
  rw [hab'] at ha
  Hint "Now `ha : r (g (f b)) = f a` and `hb : r (g (f b)) = f b`.
  Both hypotheses express `r (g (f b))` as something — so `f a = f b`.

  Since `f` is injective, `f a = f b` implies `a = b`. Use `apply hf`
  to reduce the goal to `f a = f b`."
  apply hf
  Hint "The goal is `f a = f b`. You have `ha : r (g (f b)) = f a` and
  `hb : r (g (f b)) = f b`. Chain them: `rw [← ha, hb]`."
  Hint (hidden := true) "`rw [← ha, hb]`"
  Branch
    rw [← ha]
    exact hb
  rw [← ha, hb]

Conclusion "
Congratulations — you completed **Injective World**!

## What You Learned

**The canonical injectivity proof**:
```
intro a b hab     -- assume f a = f b, prove a = b
```
Every injectivity proof starts this way. What follows depends on the
setting:
- **Arithmetic**: extract the equation (`have h : ... := hab`), then `omega`
- **Composition**: chain `apply hf` then `apply hg`
- **Extraction**: `apply hgf`, then `show` + `rw`
- **Left inverse**: instantiate `h a` and `h b`, then rewrite

**Disproving injectivity**: Find two distinct inputs with the same
output, apply injectivity to get a false equation, derive contradiction.

**Composition rules**:
| Hypothesis | Conclusion |
|---|---|
| `Injective g`, `Injective f` | `Injective (g ∘ f)` |
| `Injective (g ∘ f)` | `Injective f` |
| `LeftInverse g f` | `Injective f` |
| `Injective (g ∘ f)` | `Injective g` — **FALSE** |

**Looking ahead**: In Surjective World, you will learn the dual
story. The roles reverse in a surprising way: `Injective (g ∘ f)`
implies `Injective f` (the INNER function), but `Surjective (g ∘ f)`
implies `Surjective g` (the OUTER function!). This asymmetry — injection
tests the inner factor, surjection tests the outer factor — is one of
the deepest patterns in function theory.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith injection
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Nat.succ_injective Nat.succ.inj Nat.mul_left_cancel Nat.mul_right_cancel Nat.add_right_cancel Nat.add_left_cancel Function.Injective.comp Function.Injective.of_comp Function.LeftInverse.injective Function.HasLeftInverse.injective
