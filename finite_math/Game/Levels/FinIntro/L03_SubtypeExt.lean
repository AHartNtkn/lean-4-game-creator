import GameServer.Commands
import Mathlib

World "FinIntro"
Level 3

Title "Subtype extensionality"

Introduction
"
# Two Fin elements with the same value are equal

In Level 1, you used `⟨3, by omega⟩` to build a `Fin 5`. The angle-bracket
notation `⟨val, proof⟩` is syntactic sugar for the constructor `Fin.mk val proof`.

But here is a subtle question: if you have two elements of `Fin 5` that both
have value `2`, but were constructed with *different proofs* that `2 < 5`, are
they equal?

The answer is **yes**. Two elements of `Fin n` are equal if and only if their
underlying values are equal. The proof term is irrelevant -- only the number
matters. This is called **subtype extensionality**.

The lemma `Fin.ext_iff` captures this:
```
Fin.ext_iff : a = b ↔ a.val = b.val
```

## Your task

Below, `h₁` and `h₂` are two (potentially different) proofs that `2 < 5`.
Prove that `Fin.mk 2 h₁ = Fin.mk 2 h₂`.

Use `ext` to reduce the goal from equality of `Fin` elements to equality of
their values, then close the arithmetic goal.
"

/-- Two `Fin.mk` terms with the same value are equal, regardless of proof. -/
Statement (h₁ h₂ : 2 < 5) : Fin.mk 2 h₁ = Fin.mk 2 h₂ := by
  Hint "Use `ext` to reduce to showing that the underlying values are equal."
  ext
  Hint "The goal is now `2 = 2`. Try `rfl`."
  rfl

Conclusion
"
The proof component is irrelevant! `Fin.mk 2 h₁` and `Fin.mk 2 h₂` are
equal because they have the same `.val`, regardless of how the bound
`2 < 5` was proven.

This is a general principle for subtypes in Lean: two elements of a subtype
are equal when their underlying values are equal. For `Fin n`, this means
equality is determined entirely by the natural number, not by the proof.

The tactic `ext` (short for *extensionality*) is a general-purpose tactic
for proving equality of structured types. For `Fin`, it reduces `a = b` to
`a.val = b.val`. You will see `ext` again for other types -- it works
whenever two objects are equal if their components are equal.

When Lean sees `(2 : Fin 5)`, it automatically constructs `Fin.mk 2 (by omega)`
(or an equivalent proof). So the angle-bracket notation `⟨2, by omega⟩`
and the numeric literal `(2 : Fin 5)` produce equal elements.
"

/-- `ext` proves equality of structured types by reducing to equality of components.
For `Fin n`, `ext` reduces `a = b` to `a.val = b.val`. -/
TacticDoc ext

/-- `rfl` closes a goal of the form `a = a`. It works when both sides are
definitionally equal. -/
TacticDoc rfl

/-- `Fin.ext_iff` states that two `Fin n` elements are equal if and only if their
underlying values are equal: `a = b ↔ a.val = b.val`. The `ext` tactic applies
the forward direction automatically. -/
TheoremDoc Fin.ext_iff as "Fin.ext_iff" in "Fin"

NewTactic ext rfl
NewTheorem Fin.ext_iff
