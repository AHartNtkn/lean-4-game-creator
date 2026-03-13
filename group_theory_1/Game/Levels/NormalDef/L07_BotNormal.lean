import Game.Metadata

World "NormalDef"
Level 7

Title "⊥ is Normal"

Introduction
"
Prove that the trivial subgroup `⊥ = {1}` is normal.

Since the only element of `⊥` is `1`, you need to show that
`g * 1 * g⁻¹ ∈ ⊥` — which simplifies to `1 ∈ ⊥`.

Use the Normal constructor pattern from Level 2, then the algebra.
"

/-- Disabled — characteristic subgroups are automatically normal. -/
TheoremDoc Subgroup.normal_of_characteristic as "normal_of_characteristic" in "Normal"

/-- Disabled — `⊥` is characteristic, which implies normal. -/
TheoremDoc Subgroup.botCharacteristic as "botCharacteristic" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem Subgroup.normal_of_characteristic Subgroup.botCharacteristic

Statement (G : Type*) [Group G] : (⊥ : Subgroup G).Normal := by
  Hint "Open the Normal structure: `refine ⟨?_⟩`."
  Branch
    constructor
    intro n hn g
    rw [Subgroup.mem_bot] at hn ⊢
    rw [hn, mul_one, mul_inv_cancel]
  refine ⟨?_⟩
  Hint "Introduce the variables: `intro n hn g`."
  intro n hn g
  Hint "The goal is `g * n * g⁻¹ ∈ ⊥`. Unfold `mem_bot` at the
  hypothesis: `rw [Subgroup.mem_bot] at hn`. This gives `n = 1`."
  rw [Subgroup.mem_bot] at hn
  Hint "Now reduce the goal: `rw [Subgroup.mem_bot]`."
  rw [Subgroup.mem_bot]
  Hint "Substitute `{hn} : n = 1`: `rw [{hn}]`."
  rw [hn]
  Hint (hidden := true) "`rw [mul_one]` then `exact mul_inv_cancel g`."
  rw [mul_one]
  exact mul_inv_cancel g

Conclusion
"
`⊥` is normal because conjugating `1` always gives `1`:
`g · 1 · g⁻¹ = g · g⁻¹ = 1 ∈ ⊥`.

Combined with Level 2, you've shown both `⊤.Normal` and `⊥.Normal`.
These are the trivial cases. The interesting normality proofs require
real algebra — like the boss, where you'll prove that every kernel is
normal.
"
