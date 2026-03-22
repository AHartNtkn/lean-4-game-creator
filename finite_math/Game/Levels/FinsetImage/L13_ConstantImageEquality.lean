import Game.Metadata

World "FinsetImage"
Level 13

Title "Constant Image Equality"

Introduction "
# The Full Equality: ext Proof

Level 9 proved the forward containment: every element in the image
of a constant function equals the constant. Now prove the **full
equality**: the image of $\\{1, 2, 3\\}$ under $n \\mapsto 0$ IS
$\\{0\\}$.

This requires proving both directions:
- **Forward** ($\\subseteq$): every element in the image equals 0
  (you already know this from Level 9)
- **Backward** ($\\supseteq$): $0$ is in the image (provide a
  witness from $\\{1, 2, 3\\}$)

As in Level 6, use `ext x` to reduce equality to mutual membership.

**Your task**: Prove the full equality using `ext` and both
membership directions.
"

/-- The image of {1, 2, 3} under the constant function (n ↦ 0) is {0}. -/
Statement : (({1, 2, 3} : Finset ℕ).image (fun _ => (0 : ℕ))) = {0} := by
  Hint "Use `ext x` to prove the two finsets are equal by showing
  they have the same members."
  ext x
  Hint "The goal is an iff. Use `constructor` to split into the
  two directions."
  constructor
  · Hint "**Forward direction** (retrieval from Level 9): assume
    `h : x ∈ image (fun _ => 0) ...` and prove `x ∈ singleton 0`.
    Extract the witness, observe it maps to 0."
    intro h
    rw [Finset.mem_image] at h
    Hint "Use `obtain ⟨a, _, ha⟩ := h` to extract the witness."
    obtain ⟨a, _, ha⟩ := h
    Hint (hidden := true) "Try `rw [Finset.mem_singleton]; omega`."
    rw [Finset.mem_singleton]
    omega
  · Hint "**Backward direction**: assume `h : x ∈ singleton 0`
    (i.e., `x = 0`) and prove `x ∈ image (fun _ => 0) ...`.
    Provide a witness from the input set."
    intro h
    rw [Finset.mem_singleton] at h
    Hint "Now `h : x = 0`. Prove membership in the image by
    providing any element of the input set as the witness.
    Try `rw [Finset.mem_image]; use 1`."
    rw [Finset.mem_image]
    Hint (hidden := true) "Try `use 1`. After providing the
    witness, prove `1 ∈ ...` and `0 = x`."
    use 1
    constructor
    · Hint (hidden := true) "Try `rw [Finset.mem_insert]; left; rfl`."
      rw [Finset.mem_insert]
      left
      rfl
    · omega

Conclusion "
You proved the full equality $f(\\{1,2,3\\}) = \\{0\\}$ where
$f(n) = 0$ for all $n$. The proof combined:

1. **ext**: reduce equality to mutual membership
2. **Forward**: backward extraction shows every output is 0
3. **Backward**: forward membership with ANY witness from the set

Key insight: the backward direction only needs ONE witness from
the input set — any element works because the function is constant.

Compare cardinalities:
- Input: $|\\{1,2,3\\}| = 3$
- Output: $|\\{0\\}| = 1$

The image shrank from 3 to 1 because the function is maximally
non-injective. The next level formalizes this: the image can
NEVER be larger than the input.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.image_const Finset.image_singleton Finset.image_eq_empty
