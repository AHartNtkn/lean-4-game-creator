import Game.Metadata

World "NormalPset"
Level 1

Title "Conjugation in the Intersection"

Introduction
"
Welcome to the **Normal Subgroups Problem Set**.

Here's a warm-up combining two familiar ideas: `mem_inf` extraction
and `conj_mem`.

If `n ∈ N ⊓ K` and both subgroups are normal, then `g * n * g⁻¹`
belongs to both — so it belongs to the intersection.

Extract the components, conjugate each, and rebuild.
"

TheoremTab "Normal"

DisabledTactic simp group

Statement (G : Type*) [Group G] (N K : Subgroup G) (hN : N.Normal)
    (hK : K.Normal) (n : G) (hn : n ∈ N ⊓ K) (g : G) :
    g * n * g⁻¹ ∈ N ⊓ K := by
  Hint "Extract the components from `{hn} : n ∈ N ⊓ K` using
  `rw [Subgroup.mem_inf] at {hn}`.
  Then conjugate each component separately with `have`."
  rw [Subgroup.mem_inf] at hn
  Hint "Now `{hn} : n ∈ N ∧ n ∈ K`. Conjugate in each subgroup:
  `have h1 := hN.conj_mem n {hn}.1 g` and
  `have h2 := hK.conj_mem n {hn}.2 g`."
  have h1 := hN.conj_mem n hn.1 g
  have h2 := hK.conj_mem n hn.2 g
  Hint (hidden := true) "Rebuild the intersection membership:
  `rw [Subgroup.mem_inf]` then `exact ⟨h1, h2⟩`."
  rw [Subgroup.mem_inf]
  exact ⟨h1, h2⟩

Conclusion
"
**Component-wise conjugation**: when both subgroups are normal,
conjugation distributes over the intersection — extract, conjugate
each piece, then rebuild.

On paper: *Since `n ∈ N ∩ K`, we have `n ∈ N` and `n ∈ K`.
Normality gives `gng⁻¹ ∈ N` and `gng⁻¹ ∈ K`, so
`gng⁻¹ ∈ N ∩ K`.*

The boss of this world will wrap this argument inside a Normal
constructor.
"
