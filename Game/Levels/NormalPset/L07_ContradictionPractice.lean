import Game.Metadata

World "NormalPset"
Level 7

Title "Membership Cannot Disagree"

Introduction
"
You proved in the lecture that `a * b ∈ N` implies `b * a ∈ N`
(by choosing a strategic conjugator). What if someone claims
`b * a ∉ N`? That's a contradiction.

Derive `b * a ∈ N` from `a * b ∈ N` using the conjugation technique,
then use `contradiction` to close the goal.
"

/-- Disabled — re-derive using conjugation. -/
TheoremDoc Subgroup.Normal.mem_comm as "mem_comm" in "Normal"

/-- Disabled — re-derive using conjugation. -/
TheoremDoc Subgroup.Normal.mem_comm_iff as "mem_comm_iff" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem Subgroup.Normal.mem_comm Subgroup.Normal.mem_comm_iff

Statement (G : Type*) [Group G] (N : Subgroup G) (hN : N.Normal)
    (a b : G) (hab : a * b ∈ N) (hba : b * a ∉ N) : False := by
  Hint "Derive `b * a ∈ N` from `{hab}` using conjugation. Conjugate
  `a * b` by `a⁻¹` to move `a` from the left to the right:
  `have h := hN.conj_mem (a * b) {hab} a⁻¹`."
  Branch
    have h := hN.conj_mem' (a * b) hab a
    Hint "`{h} : a⁻¹ * (a * b) * a ∈ N`. Cancel on the left:
    `rw [inv_mul_cancel_left] at {h}`."
    rw [inv_mul_cancel_left] at h
    contradiction
  have h := hN.conj_mem (a * b) hab a⁻¹
  Hint "`{h} : a⁻¹ * (a * b) * (a⁻¹)⁻¹ ∈ N`. Clean up the double
  inverse: `rw [inv_inv] at {h}`."
  rw [inv_inv] at h
  Hint "Now cancel `a⁻¹ * a` on the left:
  `rw [inv_mul_cancel_left] at {h}`."
  rw [inv_mul_cancel_left] at h
  Hint (hidden := true) "Now `{h} : b * a ∈ N` and `{hba} : b * a ∉ N`.
  `contradiction`."
  contradiction

Conclusion
"
If `a * b ∈ N` and `N` is normal, then `b * a ∈ N` — so claiming
`b * a ∉ N` is a contradiction.

This level combines three moves:
1. **Strategic conjugator**: choose `a⁻¹` to rearrange `a * b` into
   `b * a`
2. **Store-and-clean**: `have` + `rw at h` to derive `b * a ∈ N`
3. **Contradiction**: close the goal from `h` and `hba`

On paper: *Since `ab ∈ N` and `N` is normal, conjugate by `a⁻¹`:
`a⁻¹(ab)(a⁻¹)⁻¹ = a⁻¹(ab)a = ba ∈ N` — contradicting `ba ∉ N`.*
"
