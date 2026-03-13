import Game.Metadata

World "NormalDef"
Level 2

Title "⊤ is Normal"

Introduction
"
To prove that a subgroup `N` is normal, you must construct a value of
type `N.Normal`. This is a structure with one field — the conjugation
property. Use `refine ⟨?_⟩` to open it, then `intro n hn g` to
introduce the universally quantified variables, and finally prove
`g * n * g⁻¹ ∈ N`.

Start with the easiest case: prove that `⊤` (the whole group) is
normal. Since every element belongs to `⊤`, the conjugation check
is trivial.
"

/-- Disabled — `⊤` is characteristic, which implies normal via this
instance. -/
TheoremDoc Subgroup.normal_of_characteristic as "normal_of_characteristic" in "Normal"

/-- Disabled — prove from scratch. -/
TheoremDoc Subgroup.topCharacteristic as "topCharacteristic" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem Subgroup.normal_of_characteristic Subgroup.topCharacteristic

Statement (G : Type*) [Group G] : (⊤ : Subgroup G).Normal := by
  Hint "The goal is `(⊤ : Subgroup G).Normal`. This is a structure with one
  field. Use `refine ⟨?_⟩` to open it."
  Branch
    constructor
    intro n hn g
    exact Subgroup.mem_top (g * n * g⁻¹)
  refine ⟨?_⟩
  Hint "The goal is `∀ n, n ∈ ⊤ → ∀ g, g * n * g⁻¹ ∈ ⊤`.
  Introduce the variables: `intro n hn g`."
  intro n hn g
  Hint "The goal is `g * n * g⁻¹ ∈ ⊤`. Every element belongs to `⊤` —
  use `exact Subgroup.mem_top _`."
  exact Subgroup.mem_top _

Conclusion
"
To prove `N.Normal`:
1. Open the structure: `refine ⟨?_⟩`
2. Introduce variables: `intro n hn g`
3. Prove `g * n * g⁻¹ ∈ N`

For `⊤`, step 3 is trivial — everything is in `⊤`. For real subgroups,
step 3 is where the work happens: you must show the conjugate stays in
the subgroup using algebra.

This `refine ⟨?_⟩` + `intro n hn g` opening is the standard start for
every normality proof. Memorize this pattern.
"
