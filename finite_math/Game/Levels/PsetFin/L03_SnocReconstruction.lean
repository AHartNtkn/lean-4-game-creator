import Game.Metadata

World "PsetFin"
Level 3

Title "Formula-Based Reconstruction"

Introduction "
# Reconstructing from a Formula

In FinTuples, you reconstructed tuples from explicitly given head/tail
or init/last. Here the init is described by a **formula** — you must
first compute the concrete init tuple, then apply the reconstruction
pattern.

You're given a tuple `p : Fin 3 -> NN` where:
- `hi : forall i : Fin 2, Fin.init p i = 5 * (i.val + 1)` (init described by a formula)
- `hl : p (Fin.last 2) = 15` (last element given directly)

**Strategy**:
1. Derive the concrete init: use `ext` + case split + `rw [hi]` to
   prove `Fin.init p = ![5, 10]`
2. Apply the snoc reconstruction pattern:
   `have key := (vecSnoc_self_init p).symm`, then `rw` known values
"

/-- Reconstruct a tuple whose init is described by a formula. -/
Statement (p : Fin 3 → ℕ)
    (hi : ∀ i : Fin 2, Fin.init p i = 5 * (i.val + 1))
    (hl : p (Fin.last 2) = 15) :
    p = vecSnoc ![5, 10] 15 := by
  Hint "Two phases: first derive `Fin.init p = ![5, 10]` using
  ext + formula rewrite + case split. Then apply snoc reconstruction."
  have hi2 : Fin.init p = ![5, 10] := by
    Hint "Inside the `have`, use `ext ⟨v, hv⟩` to check the formula at
    each index. After `rw [hi]`, each index reduces to an arithmetic check."
    Hint (hidden := true) "Use `ext ⟨v, hv⟩`, then `rw [hi]`, then
    case-split on `v` with `cases v with | zero | succ n`"
    ext ⟨v, hv⟩
    rw [hi]
    cases v with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ m => exact absurd hv (by omega)
  Hint (hidden := true) "Now apply snoc reconstruction:
  `have key := (vecSnoc_self_init p).symm`, then
  `rw [hl, hi2] at key; exact key`."
  have key := (vecSnoc_self_init p).symm
  rw [hl, hi2] at key
  exact key

Conclusion "
This is a harder variant of the snoc reconstruction: instead of the
init being given as an explicit tuple, it was described by a formula.
You had to:

1. **Compute** the concrete init by ext + case split + formula rewrite
2. **Reconstruct** the full tuple with the standard `.symm` + `rw at` pattern

This two-phase approach — derive concrete data from abstract
descriptions, then apply known patterns — is common in formal
mathematics.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
