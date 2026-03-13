import Game.Metadata

World "HomDef"
Level 1

Title "The `simp` Tactic"

Introduction
"
Before we meet homomorphisms, let's learn a powerful new tool: the `simp`
tactic.

`simp` works by repeatedly applying lemmas tagged with `@[simp]` until
it can't make further progress. Many of the group lemmas you already know
— `mul_inv_cancel`, `inv_mul_cancel`, `mul_one`, `one_mul` — are tagged
this way.

Try using `simp` to close this goal in a single step. It will
automatically find and apply the right lemmas.
"

/-- The `simp` tactic simplifies the goal by repeatedly applying lemmas
tagged with `@[simp]`.

**Basic usage**: `simp` tries all known simp lemmas automatically.

**Directed usage**: `simp [h1, h2]` adds `h1` and `h2` to the lemma set.
Use this when bare `simp` doesn't close the goal, or when you want to
include hypotheses from the context.

**Warning**: `simp` is powerful but can be opaque. If `simp` doesn't work,
try `simp [specific_lemma]` or fall back to manual `rw` steps. -/
TacticDoc simp

NewTactic simp

TheoremTab "Group"

DisabledTactic group

Statement (G : Type*) [Group G] (a : G) : a * a⁻¹ * 1 = 1 := by
  Hint "Try `simp`. It will find the right lemmas (`mul_inv_cancel`,
  `one_mul`) and close the goal automatically."
  simp

Conclusion
"
One tactic, and the goal vanished. Under the hood, `simp` applied
`mul_inv_cancel` to get `a * a⁻¹ → 1`, then `one_mul` to get
`1 * 1 → 1`.

You could also write `simp [mul_inv_cancel]` to explicitly name
the lemma — this is called **directed simplification**. You'll
see why that matters in the next level.
"
