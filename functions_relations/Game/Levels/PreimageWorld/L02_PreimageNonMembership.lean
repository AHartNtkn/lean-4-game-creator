import Game.Metadata

World "PreimageWorld"
Level 2

Title "Preimage Non-Membership"

TheoremTab "Set"

Introduction "
# When an Element is NOT in a Preimage

In the last level, you proved that 3 is in a preimage by showing
`f 3 ∈ t`. What about elements that are **not** in a preimage?

$x \\notin f^{-1}(t)$ means $f(x) \\notin t$.

Since `∉` is `¬ ∈`, the proof shape is: assume `x ∈ f ⁻¹' t`
(i.e., `f x ∈ t`), then derive a contradiction.

**Your task**: Prove that 10 is NOT in the preimage of `{n | n < 5}`
under `n ↦ n + 1`. This means `10 + 1 < 5` is false (since `11 ≥ 5`).

**Proof plan**:
1. `show ¬ (10 + 1 < 5)` — unfold the preimage membership to
   arithmetic (just like using `show` in Set World)
2. `omega` — close the arithmetic goal
"

/-- 10 is not in the preimage because 10 + 1 = 11, which is not less than 5. -/
Statement : (10 : ℕ) ∉ (fun n : ℕ => n + 1) ⁻¹' {n | n < 5} := by
  Hint "The goal is `10 ∉ f ⁻¹' t`. Recall that `∉` means `¬ ∈`.
  Preimage membership unfolds to `10 + 1 < 5`, so the goal is
  `¬ (10 + 1 < 5)`. Use `show ¬ (10 + 1 < 5)` to make this explicit."
  Hint (hidden := true) "`show ¬ (10 + 1 < 5)` then `omega`."
  Branch
    intro (h : 10 + 1 < 5)
    omega
  show ¬ (10 + 1 < 5)
  omega

Conclusion "
You proved preimage non-membership by unfolding and arithmetic:

1. **Unfold**: `10 ∉ f ⁻¹' t` means `¬(10 + 1 < 5)`
2. **Compute**: `¬(11 < 5)` is true

This is the same pattern as non-membership in Set World
(`7 ∉ {n | n < 5}` became `¬(7 < 5)` via `show`), with one extra
step: the function is applied first.

**Pattern**: To prove `x ∉ f ⁻¹' t`:
1. `intro h` — assume `x ∈ f ⁻¹' t` (i.e., `f x ∈ t`)
2. Derive a contradiction from `h`

**In plain math**: \"$10 \\notin f^{-1}(\\{n \\mid n < 5\\})$ because
$f(10) = 11$ and $11 \\not< 5$.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
