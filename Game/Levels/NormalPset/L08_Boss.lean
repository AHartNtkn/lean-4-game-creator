import Game.Metadata

World "NormalPset"
Level 8

Title "Boss — Intersection of Normals Is Normal"

Introduction
"
Prove that the intersection of two normal subgroups is normal.

You proved the inner fact in Level 1: if `n ∈ N ⊓ K` and both
subgroups are normal, then `g * n * g⁻¹ ∈ N ⊓ K`.

Now wrap that argument inside the Normal constructor:
`refine ⟨?_⟩` + `intro n hn g`.
"

/-- Disabled — you are proving this yourself. -/
TheoremDoc Subgroup.normal_inf_normal as "normal_inf_normal" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem Subgroup.normal_inf_normal

Statement (G : Type*) [Group G] (N K : Subgroup G) (hN : N.Normal)
    (hK : K.Normal) : (N ⊓ K).Normal := by
  Hint "Build the Normal structure: `refine ⟨?_⟩`."
  Branch
    constructor
    intro n hn g
    rw [Subgroup.mem_inf] at hn ⊢
    exact ⟨hN.conj_mem n hn.1 g, hK.conj_mem n hn.2 g⟩
  refine ⟨?_⟩
  Hint "Introduce the variables: `intro n hn g`."
  intro n hn g
  Hint "Extract the components from `{hn} : n ∈ N ⊓ K`:
  `rw [Subgroup.mem_inf] at {hn}`.
  Then conjugate each component with `have`."
  rw [Subgroup.mem_inf] at hn
  have h1 := hN.conj_mem n hn.1 g
  have h2 := hK.conj_mem n hn.2 g
  Hint (hidden := true) "Rebuild: `rw [Subgroup.mem_inf]` then
  `exact ⟨h1, h2⟩`."
  rw [Subgroup.mem_inf]
  exact ⟨h1, h2⟩

Conclusion
"
Congratulations on completing the **Normal Subgroups Problem Set**!

You proved that the intersection of two normal subgroups is normal.
Combined with the lecture world:

| Subgroup | Normal? |
|----------|---------|
| `⊤` | Always (Level 2 of the lecture) |
| `⊥` | Always (Level 7 of the lecture) |
| `ker(f)` | Always (boss of the lecture) |
| `N ⊓ K` | When both `N` and `K` are normal (this boss) |

The normal subgroups of `G` form a **sublattice** of the subgroup
lattice — they are closed under intersection (and, it turns out,
under the join operation too).

The boss used the **decompose-operate-rebuild** strategy: break a
membership condition defined by a conjunction (`⊓`), operate on each
component separately, then reassemble. You first used this pattern
for `⊓` in SubgroupBasics, and it will return whenever membership is
defined by multiple conditions — including direct products later.

Proof moves practiced:

| Move | Pattern |
|------|---------|
| **Component-wise conjugation** | Extract from `⊓`, conjugate each, rebuild |
| **De-conjugation** | Conjugate back to undo `gng⁻¹` |
| **Strategic conjugator** | Choose conjugator to rearrange a product |
| **Contradiction-setup** | Derive positive fact, then `contradiction` |
| **Product conjugation** | Combine via `mul_mem`, then `conj_mem` |
| **Representative absorption** | `(an)N = aN` via `leftCoset_eq_iff` |

On paper: *If `N, K ◁ G` and `n ∈ N ∩ K`, then for any `g ∈ G`:
`gng⁻¹ ∈ N` (since `N` is normal) and `gng⁻¹ ∈ K` (since `K` is
normal), so `gng⁻¹ ∈ N ∩ K`. Hence `N ∩ K` is normal.*

What's next: you'll explore the **normalizer** of a subgroup — the
largest subgroup in which a given subgroup is normal. Notice that
normality means *every* element of `G` conjugates `N` back into
itself. What if `N` is not normal? Then only *some* elements `g`
satisfy `gng⁻¹ ∈ N` for all `n` — those elements form the
normalizer.
"
