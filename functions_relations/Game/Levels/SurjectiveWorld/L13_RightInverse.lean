import Game.Metadata

World "SurjectiveWorld"
Level 13

Title "Right Inverses Imply Surjectivity"

TheoremTab "Function"

Introduction "
# Right Inverses

A function `g : β → α` is a **right inverse** of `f : α → β` if
`f ∘ g = id`, meaning `f (g x) = x` for every `x`.

In Lean, this is `Function.RightInverse g f`:

$$\\text{RightInverse}(g, f) \\;\\;:\\equiv\\;\\; \\forall\\, x,\\;\\; f(g(x)) = x$$

**Key theorem**: If `f` has a right inverse, then `f` is surjective.

The idea: for any `b : β`, the witness is `g b`. Since `g` is a right
inverse, `f (g b) = b` holds by definition.

**Compare with Injective World**: There, you proved that a
LEFT inverse implies INJECTIVITY. Here, a RIGHT inverse implies
SURJECTIVITY. The duality:

| Inverse type | Implies |
|---|---|
| Left inverse: `g (f x) = x` | `f` is injective |
| Right inverse: `f (g x) = x` | `f` is surjective |

A left inverse \"remembers\" the original input (injectivity). A right
inverse \"provides\" a preimage for every output (surjectivity).
"

/-- `Function.RightInverse g f` means that `g` is a right inverse
of `f`: `f (g x) = x` for every `x`. Equivalently, `f ∘ g = id`.

## Syntax
```
h : Function.RightInverse g f
h x : f (g x) = x           -- apply to a specific element
```

## When to use it
When you need to produce a preimage of `b` under `f`. If `h` is a
proof of `RightInverse g f`, then `g b` is a preimage: `h b` proves
`f (g b) = b`.

## Example
```
-- h : Function.RightInverse g f, b : β
have hb := h b    -- hb : f (g b) = b
```

## Connection to surjectivity
If `f` has a right inverse `g`, then `f` is surjective: for any `b`,
the witness is `g b`.

## Connection to left inverse
`RightInverse g f` is the same as `LeftInverse f g`: saying `g` is a
right inverse of `f` is the same as saying `f` is a left inverse of `g`.
-/
DefinitionDoc Function.RightInverse as "Function.RightInverse"

/-- If f has a right inverse g, then f is surjective. -/
Statement {α β : Type} {g : β → α} {f : α → β}
    (h : Function.RightInverse g f) : Function.Surjective f := by
  Hint "Start with `intro b` as always for a surjectivity proof."
  intro b
  Hint "You need `a` with `f a = b`. Since `h : RightInverse g f` means
  `f (g x) = x` for all `x`, the witness is `g b`:

  `use g b`."
  use g b
  Hint "The goal is `f (g b) = b`. This is exactly `h b` — the right
  inverse property applied to `b`.

  Use `exact h b`."
  exact h b

Conclusion "
You proved that right inverses imply surjectivity!

```
intro b       -- arbitrary output
use g b       -- witness: apply the right inverse
exact h b     -- f (g b) = b by definition of right inverse
```

**Why it is so clean**: A right inverse directly hands you a preimage
machine. For any `b`, feed it to `g` and you get a preimage. The
verification is just the definition of right inverse.

**The duality table** (now complete):

| Hypothesis | Conclusion | Proof idea |
|---|---|---|
| `LeftInverse g f` | `Injective f` | `g` recovers original inputs |
| `RightInverse g f` | `Surjective f` | `g` provides preimages |

**Sections**: A right inverse of a surjection is often called a **section**
in mathematics — it \"selects\" one element from each fiber. You will
encounter sections throughout algebra, topology, and bundle theory.

**The Axiom of Choice connection**: You just proved that a right inverse
implies surjectivity. The converse — that every surjective function has
a right inverse — is equivalent to the **Axiom of Choice**. The idea:
if `f` is surjective, then for each `b` there exists a preimage, but
*choosing* one preimage for every `b` simultaneously requires Choice.
This is one of the most important facts about surjections in mathematics.

**Why we cannot prove the converse constructively**: The forward direction
(this level) is constructive: given `g`, the witness for surjectivity at
`b` is just `g b`. The converse requires building `g` by making
infinitely many choices — one for each `b`. In constructive logic, `∃ a, f a = b`
does not give you a *computable* `a`; it only asserts existence. Lean 4
includes the Axiom of Choice (`Classical.choice`), so the converse IS
provable — you will prove it in the next level using `Exists.choose`.

**Looking ahead**: In the next level, you will construct a right inverse
from a surjective function using Choice. After that, the boss combines
surjectivity with injectivity.
"

NewDefinition Function.RightInverse

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.RightInverse.surjective Function.HasRightInverse.surjective Function.Surjective.comp
