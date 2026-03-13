import Game.Metadata

World "CosetBasics"
Level 9

Title "Boss — Coset Equality Is an Equivalence Relation"

Introduction
"
Package the three properties you just proved — reflexivity, symmetry,
and transitivity — into a single `Equivalence` structure.

An `Equivalence r` bundles:
- `refl : ∀ x, r x x`
- `symm : ∀ {x y}, r x y → r y x`
- `trans : ∀ {x y z}, r x y → r y z → r x z`

Use `refine ⟨?_, ?_, ?_⟩` to split into three subgoals. Each subgoal
is a proof you completed in the last three levels.
"

/-- An `Equivalence r` proves that the relation `r` is reflexive,
symmetric, and transitive. Construct with `refine ⟨?_, ?_, ?_⟩`. -/
DefinitionDoc Equivalence as "Equivalence"

NewDefinition Equivalence

/-- Disabled — you are proving this yourself. -/
TheoremDoc leftCosetEquivalence_rel as "leftCosetEquivalence_rel" in "Coset"

/-- Disabled — blocks direct construction of the equivalence. -/
TheoremDoc QuotientGroup.leftRel_eq as "QuotientGroup.leftRel_eq" in "Coset"

/-- Disabled — blocks reconstruction of `leftRel_eq` via `funext₂ + propext`. -/
TheoremDoc QuotientGroup.leftRel_apply as "QuotientGroup.leftRel_apply" in "Coset"

TheoremTab "Coset"

DisabledTactic simp group
DisabledTheorem leftCosetEquivalence_rel QuotientGroup.leftRel_eq QuotientGroup.leftRel_apply

Statement (G : Type*) [Group G] (H : Subgroup G) :
    Equivalence (fun a b : G => a⁻¹ * b ∈ H) := by
  Hint "Split into three subgoals: `refine ⟨?_, ?_, ?_⟩`."
  Branch
    constructor
    · intro x
      rw [inv_mul_cancel]
      exact H.one_mem
    · intro x y h
      rw [← inv_inv x]
      rw [← mul_inv_rev]
      exact H.inv_mem h
    · intro x y z h1 h2
      rw [← mul_inv_cancel_left y z]
      rw [← mul_assoc]
      exact H.mul_mem h1 h2
  refine ⟨?_, ?_, ?_⟩
  · -- Reflexivity
    Hint "**Reflexivity**: introduce `x` with `intro x`, then prove
    `x⁻¹ * x ∈ H`. This is the same proof as Level 6."
    intro x
    rw [inv_mul_cancel]
    exact H.one_mem
  · -- Symmetry
    Hint "**Symmetry**: introduce variables with `intro x y h`.
    This is the same proof as Level 7."
    intro x y h
    rw [← inv_inv x]
    rw [← mul_inv_rev]
    exact H.inv_mem h
  · -- Transitivity
    Hint "**Transitivity**: introduce variables with `intro x y z h1 h2`.
    This is the same proof as Level 8."
    intro x y z h1 h2
    rw [← mul_inv_cancel_left y z]
    rw [← mul_assoc]
    exact H.mul_mem h1 h2

Conclusion
"
You proved that `a⁻¹b ∈ H` is an equivalence relation on `G`.
This partitions `G` into disjoint **left cosets** of `H`.

On paper: *Define `a ~ b` iff `a⁻¹b ∈ H`. Reflexive: `a⁻¹a = 1 ∈ H`.
Symmetric: if `a⁻¹b ∈ H`, then `b⁻¹a = (a⁻¹b)⁻¹ ∈ H`.
Transitive: if `a⁻¹b ∈ H` and `b⁻¹c ∈ H`, then
`a⁻¹c = (a⁻¹b)(b⁻¹c) ∈ H`.*

This equivalence relation is exactly the one that defines the quotient
`G ⧸ H`. When `H` is a **normal** subgroup, `G ⧸ H` becomes a group —
that's the quotient group construction you'll reach after studying
normality. Without normality, the equivalence classes exist but the
natural multiplication `(aH)(bH) = (ab)H` fails — the result depends
on which representatives you pick, not just which cosets.

**Warning**: There are also *right* cosets `Ha = {h * a | h ∈ H}`. In a
non-abelian group, the left coset `aH` and the right coset `Ha` can be
different sets. For example, in `S₃` with `H = {1, (12)}` and
`a = (123)`: the left coset `(123)H = {(123), (13)}` but the right
coset `H(123) = {(123), (23)}`. A subgroup where left and right cosets
always agree is called **normal**.

Proof moves learned:
- **Coset-membership unfold**: `rw [mem_leftCoset_iff]` reduces `x ∈ aH`
  to `a⁻¹x ∈ H`
- **Coset-equality move**: `rw [leftCoset_eq_iff]` reduces `aH = bH` to
  `a⁻¹b ∈ H`
- **Inverse-flip**: `b⁻¹a = (a⁻¹b)⁻¹` via `← inv_inv` then
  `← mul_inv_rev`
- **Insert-cancel**: `a⁻¹c = (a⁻¹b)(b⁻¹c)` via `← mul_inv_cancel_left`
  then `← mul_assoc`
"
