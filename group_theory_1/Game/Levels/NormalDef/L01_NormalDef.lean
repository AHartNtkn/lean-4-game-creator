import Game.Metadata

World "NormalDef"
Level 1

Title "Normal Subgroups"

Introduction
"
A subgroup `N` of `G` is **normal** if it is closed under conjugation:
for every `n ∈ N` and every `g ∈ G`, we have `g * n * g⁻¹ ∈ N`.

In Lean, this is the structure `Subgroup.Normal`:

`Subgroup.Normal N` means `∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N`

The defining property is accessed via `Subgroup.Normal.conj_mem`:

`hN.conj_mem n hn g : g * n * g⁻¹ ∈ N`

where `hN : N.Normal`, `hn : n ∈ N`, and `g : G`.

Given that `N` is normal, `n ∈ N`, and `g : G`, prove
`g * n * g⁻¹ ∈ N`.
"

/-- A subgroup `N` of `G` is **normal** if it is closed under
conjugation: for every `n ∈ N` and every `g ∈ G`, the element
`g * n * g⁻¹` also belongs to `N`.

In Lean: `Subgroup.Normal N` means `∀ n ∈ N, ∀ g, g * n * g⁻¹ ∈ N`. -/
DefinitionDoc Subgroup.Normal as "Subgroup.Normal"

NewDefinition Subgroup.Normal

/-- `hN.conj_mem n hn g` says: if `hN : N.Normal`, `hn : n ∈ N`, and
`g : G`, then `g * n * g⁻¹ ∈ N`.

This is the defining property of a normal subgroup. Use it to
extract the conjugation closure guarantee from a normality hypothesis. -/
TheoremDoc Subgroup.Normal.conj_mem as "Subgroup.Normal.conj_mem" in "Normal"

NewTheorem Subgroup.Normal.conj_mem

TheoremTab "Normal"

DisabledTactic simp group

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (n : G) (hn : n ∈ N) (g : G) : g * n * g⁻¹ ∈ N := by
  Hint "The goal is `g * n * g⁻¹ ∈ N`. Since `N` is normal, this is
  exactly what `Subgroup.Normal.conj_mem` provides.

  Use `exact hN.conj_mem n hn g`."
  exact hN.conj_mem n hn g

Conclusion
"
You used the defining property of a normal subgroup: if `N` is normal,
then `g * n * g⁻¹ ∈ N` for any `n ∈ N` and any `g ∈ G`.

**Not every subgroup is normal.** Consider the symmetric group S₃ and
the subgroup `H = {id, (1 2)}`. Conjugating `(1 2)` by `(1 3)` gives:

`(1 3) · (1 2) · (1 3)⁻¹ = (2 3) ∉ H`

So `H` is not normal in S₃. The element \"escapes\" the subgroup under
conjugation.

On the other hand, `{id, (1 2 3), (1 3 2)}` *is* normal in S₃ — every
conjugate of a 3-cycle is another 3-cycle, which stays in the subgroup.

To *prove* that a subgroup is normal, you must show that conjugation
by any group element preserves membership. This is the
**conjugation-check** move, and you'll practice it next.
"
