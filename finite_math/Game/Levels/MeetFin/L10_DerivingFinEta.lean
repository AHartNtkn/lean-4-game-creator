import Game.Metadata

World "MeetFin"
Level 10

Title "Deriving Fin.eta"

Introduction "
# The Reconstruction Identity

In Level 9, you proved that a `Fin` element with a known value equals
its explicit reconstruction: given `h : i.val = 3`, you showed
`i = ⟨3, by omega⟩`.

Now prove the **general** version: every `Fin` element equals its
own reconstruction from components, with no hypothesis needed.

The statement is: for any `i : Fin (n + 1)`,
$$i = \\langle i.\\text{val}, i.\\text{isLt} \\rangle$$

This is called **`Fin.eta`** — the reconstruction identity.
It says that taking a `Fin` element apart (extracting `.val` and `.isLt`)
and putting it back together (with `⟨_, _⟩`) gives back the original.

**Strategy**: Use `rw [Fin.ext_iff]` to reduce to a value equality.
The resulting goal is `i.val = i.val`, which is `rfl`.
"

/-- Every Fin element equals its own reconstruction from components. -/
Statement (n : ℕ) (i : Fin (n + 1)) : i = ⟨i.val, i.isLt⟩ := by
  Hint "Use `rw [Fin.ext_iff]` to reduce the `Fin` equality to a
  value equality. The resulting goal `i.val = i.val` is reflexive,
  so the rewrite closes the goal in one step."
  Hint (hidden := true) "`rw [Fin.ext_iff]` transforms the goal to
  `i.val = i.val` and closes it automatically."
  rw [Fin.ext_iff]

Conclusion "
You just **derived** `Fin.eta` — the fact that every `Fin` element
equals its reconstruction from `.val` and `.isLt`.

The proof was one step: `rw [Fin.ext_iff]`. The rewrite transforms
`i = ⟨i.val, i.isLt⟩` into `i.val = i.val`, and since this is
reflexive, the goal closes automatically. This is the
`ext_iff` pattern at its simplest: reduce to values, and the equality
is reflexive.

`Fin.eta` is a named lemma in Mathlib, and it's an instance of a
more general principle: **`Subtype.eta`**. For any subtype
`{ x : alpha // P x }`, an element equals `⟨x.val, x.property⟩`.
The proof is always the same: extensionality plus reflexivity.

We'll continue using the two-step `rw [Fin.ext_iff]` + close pattern
rather than citing `Fin.eta` directly, because the two-step version is
more flexible — it works even when the reconstruction isn't exact
(e.g., when the value comes from a hypothesis rather than from `.val`
itself, as you saw in Level 9).
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
