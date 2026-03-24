import Game.Metadata

World "PsetImgPreimg"
Level 2

Title "Concrete: Computing an Image"

TheoremTab "Set"

Introduction "
# Computing an Image Concretely

Every other level in this problem set works with ABSTRACT functions
and sets. This level grounds the theory in a specific computation.

Consider the successor function `Nat.succ : ℕ → ℕ` (which maps `n`
to `n + 1`). What is the image of the set of naturals less than 3
under `Nat.succ`?

$$\\text{succ}(\\{0, 1, 2\\}) = \\{1, 2, 3\\}$$

That is, the set of natural numbers `m` with `0 < m` and `m ≤ 3`.

The proof uses the same `ext` + `constructor` pattern as the abstract
levels, but now the witness arithmetic becomes visible.

**Forward**: given `x < 3`, show `0 < x + 1` and `x + 1 ≤ 3`.

**Backward**: given `0 < y` and `y ≤ 3`, the witness is `y - 1`.

**Tip**: When a hypothesis or goal involves set membership defined
by a predicate, that membership is definitionally `P x`. Use
`have h' : P x := h` to convert a set membership hypothesis into
its arithmetic form, or `show P x` to convert a set membership goal.
This lets `omega` see the arithmetic.

**Observations** (keep these in mind for later worlds):
- `Nat.succ` is **injective**: different inputs always give different
  outputs.
- `Nat.succ` is **NOT surjective**: `0` has no preimage.
"

/-- The image of {0, 1, 2} under the successor function is {1, 2, 3}. -/
Statement : Nat.succ '' {n : ℕ | n < 3} = {m : ℕ | 0 < m ∧ m ≤ 3} := by
  Hint "Start with `ext y` then `constructor` to prove set equality."
  ext y
  constructor
  -- Forward: y ∈ Nat.succ '' {n | n < 3} → y ∈ {m | 0 < m ∧ m ≤ 3}
  · Hint "Destructure the image membership with `rintro ⟨x, hx, rfl⟩`.
    Then convert `hx` to arithmetic with `have hx' : x < 3 := hx`
    so `omega` can use it."
    Hint (hidden := true) "`rintro ⟨x, hx, rfl⟩` then
    `have hx' : x < 3 := hx` then `constructor` then `omega`
    then `omega`."
    Branch
      intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : x < 3 := hx
      constructor
      · omega
      · omega
    rintro ⟨x, hx, rfl⟩
    have hx' : x < 3 := hx
    constructor
    · omega
    · omega
  -- Backward: y ∈ {m | 0 < m ∧ m ≤ 3} → y ∈ Nat.succ '' {n | n < 3}
  · Hint "The witness is `y - 1`. Start with `intro hy` then
    `obtain ⟨hpos, hle⟩ := hy` to get the arithmetic hypotheses.
    Then `use y - 1` and verify the conditions."
    Hint (hidden := true) "`intro hy` then `obtain ⟨hpos, hle⟩ := hy`
    then `use y - 1` then `constructor` then `show y - 1 < 3` then
    `omega` then `omega`."
    Branch
      intro hy
      obtain ⟨hpos, hle⟩ := hy
      use y - 1
      constructor
      · show y - 1 < 3; omega
      · omega
    intro hy
    obtain ⟨hpos, hle⟩ := hy
    use y - 1
    constructor
    · show y - 1 < 3
      omega
    · omega

Conclusion "
You computed that the image of the set of naturals less than 3 under
`Nat.succ` equals the set of naturals `m` with `0 < m` and `m ≤ 3` —
in other words, the three-element set containing 1, 2, and 3.

The proof followed the SAME pattern as abstract image proofs:
1. `ext y; constructor` — set equality via biconditional
2. Forward: `rintro ⟨x, hx, rfl⟩` — destructure image membership
3. Backward: provide witness `y - 1` and verify conditions

**New technique**: `have h' : x < 3 := h` converts a set membership
hypothesis into arithmetic form that `omega` can use. Similarly,
`show y - 1 < 3` converts a set membership goal. This is because
set membership defined by a predicate is definitionally `P x` —
`have` and `show` exploit this definitional equality.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith mono gcongr
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.mem_image_of_mem Iff.rfl
