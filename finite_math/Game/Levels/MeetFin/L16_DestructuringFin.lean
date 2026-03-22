import Game.Metadata

World "MeetFin"
Level 16

Title "Destructuring Fin"

Introduction "
# Destructuring Fin Elements

So far, you've accessed the parts of a `Fin n` element using dot
notation: `x.val` and `x.isLt`. There's another way:
**destructuring** with `cases`.

When you write:
```
cases x with | mk v hlt =>
```
Lean replaces `x : Fin 3` with two new hypotheses:
- `v : ℕ` — the underlying value
- `hlt : v < 3` — the bound proof

This is the same information as `x.val` and `x.isLt`, but now they're
standalone variables in your context.

Why learn a second way to access these? Because in the next level,
you'll need to **case-split on the value itself** — asking whether
`v = 0`, `v = 1`, or something else. That requires `v` as a standalone
variable, which destructuring provides.

**Your task**: Prove that every element of `Fin 3` can be reconstructed
from a natural number and a bound proof. In other words, show there
exist `v` and `h : v < 3` such that `x = ⟨v, h⟩`.

Destructure `x` first — after that, the components are right there in
your context and you can package them up.
"

/-- Every Fin element can be reconstructed from its components. -/
Statement (x : Fin 3) : ∃ (v : ℕ) (h : v < 3), x = ⟨v, h⟩ := by
  Hint "Destructure `x` into its components:
  `cases x with | mk v hlt =>`"
  cases x with
  | mk v hlt =>
    Hint "Now you have `v : ℕ` and `hlt : v < 3` as standalone
    variables. The goal asks for a number and a bound proof such that
    the element equals the reconstruction. You already have both!
    Use `exact ⟨v, hlt, rfl⟩` to provide `v` as the number, `hlt`
    as the bound proof, and `rfl` for the equality (since the element
    IS its own reconstruction)."
    exact ⟨v, hlt, rfl⟩

Conclusion "
You've just destructured a `Fin` element for the first time.

The pattern `cases x with | mk v hlt =>` is the `Fin` version of
a general Lean pattern: any structure (or subtype) can be taken
apart with `cases` to expose its components.

| Before destructuring | After |
|---|---|
| `x : Fin 3` | `v : ℕ`, `hlt : v < 3` |
| `x.val` | `v` |
| `x.isLt` | `hlt` |

After destructuring, the components are standalone variables that
you can use directly — as existential witnesses, in case splits, or
in any other tactic that needs a named term. The equality
`⟨v, hlt⟩ = ⟨v, hlt⟩` closes by `rfl` because the element IS its
own reconstruction from components.

**Alternative: `obtain`**. There is another way to destructure in
Lean: `obtain ⟨v, hlt⟩ := x`. This does the same thing as
`cases x with | mk v hlt =>` when the type has exactly one
constructor (as `Fin` does — its only constructor is `mk`). Use
`cases` when you need to enumerate multiple constructors (like
`Nat.zero` and `Nat.succ`); use `obtain` when there's only one
constructor and you just want to extract the components. Both
are common in real Lean code.

You'll need destructuring in the next level for full case analysis.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
