import Game.Metadata

World "PsetSets"
Level 1

Title "Universal Set and Complement"

TheoremTab "Set"

Introduction "
# Problem Set: Level 1

Welcome to the Sets Problem Set! This level warms you up with a
fundamental identity:

$$\\text{Set.univ} \\setminus s = s^c$$

In words: removing `s` from the universal set gives exactly the
complement of `s`. This is almost the *definition* of complement,
expressed in terms of set difference.

The proof is short — a good starting point for the problem set.
"

/-- Removing s from univ gives the complement. -/
Statement (α : Type) (s : Set α) : Set.univ \ s = sᶜ := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ Set.univ \ s → x ∈ sᶜ
  · Hint "**Forward**: `x ∈ Set.univ \\ s` means `x ∈ Set.univ ∧ x ∉ s`.
    The second component is what you need."
    Hint (hidden := true) "`intro hx` then `exact hx.2`."
    intro hx
    exact hx.2
  -- Backward: x ∈ sᶜ → x ∈ Set.univ \ s
  · Hint "**Backward**: `x ∈ sᶜ` means `x ∉ s`. You need
    `x ∈ Set.univ ∧ x ∉ s`. The first part uses `Set.mem_univ x`."
    Hint (hidden := true) "`intro hx` then `exact ⟨Set.mem_univ x, hx⟩`."
    intro hx
    exact ⟨Set.mem_univ x, hx⟩

Conclusion "
You proved `Set.univ \\ s = sᶜ`. This says the complement of `s` IS
the difference of the universe and `s`.

**`Set.mem_univ`**: The proof used `Set.mem_univ x`, which states
`x ∈ Set.univ` for any `x`. This is `True` — every element belongs to
the universal set. You saw this tool in Indexed Operations World when
proving that remainder classes cover all of `Nat`.

**Mathematical context**: In a universe `α`, every set `s : Set α`
lives inside `Set.univ`. The complement `sᶜ` collects everything NOT
in `s`. The identity `Set.univ \\ s = sᶜ` makes this precise: the
complement is the residual of `s` within the universe.
"

/-- `Set.univ_diff` states `Set.univ \\ s = sᶜ`. -/
TheoremDoc Set.univ_diff as "Set.univ_diff" in "Set"

/-- `top_sdiff` is the lattice version: `⊤ \\ a = aᶜ`. -/
TheoremDoc top_sdiff as "top_sdiff" in "Set"

/-- `le_antisymm` states `a ≤ b → b ≤ a → a = b` (lattice antisymmetry). -/
TheoremDoc le_antisymm as "le_antisymm" in "Set"

/-- `sup_le` states `a ≤ c → b ≤ c → a ⊔ b ≤ c` (lattice join bound). -/
TheoremDoc sup_le as "sup_le" in "Set"

/-- `inf_le_left` states `a ⊓ b ≤ a` (lattice meet projection). -/
TheoremDoc inf_le_left as "inf_le_left" in "Set"

/-- `le_sup_left` states `a ≤ a ⊔ b` (lattice join inclusion). -/
TheoremDoc le_sup_left as "le_sup_left" in "Set"

/-- `le_sup_right` states `b ≤ a ⊔ b` (lattice join inclusion). -/
TheoremDoc le_sup_right as "le_sup_right" in "Set"

/-- `inf_le_right` states `a ⊓ b ≤ b` (lattice meet projection). -/
TheoremDoc inf_le_right as "inf_le_right" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.univ_diff top_sdiff le_antisymm sup_le inf_le_left le_sup_left le_sup_right inf_le_right
