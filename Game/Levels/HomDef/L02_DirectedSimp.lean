import Game.Metadata

World "HomDef"
Level 2

Title "Directed Simplification"

Introduction
"
In the last level, bare `simp` closed the goal automatically because
all the needed lemmas were already tagged `@[simp]`.

But `simp` doesn't automatically use hypotheses from your context.
If you have `h : a = b⁻¹` in your hypotheses, bare `simp` won't
substitute `b⁻¹` for `a` — you have to tell it: `simp [h]`.

The syntax `simp [h]` adds `h` to the lemma set that `simp` uses.
You can list multiple items: `simp [h1, h2, lemma_name]`.

Try it: use `simp [h]` to close this goal. You could also solve
it manually with `rw`, but the `simp [h]` approach is what you'll
use most often going forward.
"

TheoremTab "Group"

DisabledTactic group

Statement (G : Type*) [Group G] (a b : G) (h : a = b⁻¹) :
    a * b = 1 := by
  Hint "Bare `simp` won't work here — it doesn't know about `{h}`.
  Try `simp [{h}]` to include the hypothesis."
  Branch
    rw [h, inv_mul_cancel]
  simp [h]

Conclusion
"
`simp [{h}]` first substituted `b⁻¹` for `a` (using `{h}`), then
applied `inv_mul_cancel` to close `b⁻¹ * b = 1`.

The manual proof is `rw [{h}, inv_mul_cancel]` — two rewrites. The
`simp [{h}]` version is shorter because `simp` handles the chain
automatically.

**Key insight**: `simp` does not use local hypotheses by default.
When you need `simp` to use a hypothesis `h`, write `simp [{h}]`.
This pattern will be essential when working with homomorphisms.
"
