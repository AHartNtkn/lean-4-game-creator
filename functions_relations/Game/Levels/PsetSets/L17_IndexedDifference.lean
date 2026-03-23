import Game.Metadata

World "PsetSets"
Level 17

Title "Indexed Difference"

TheoremTab "Set"

Introduction "
# Problem Set: Level 17

Prove that set difference distributes over indexed union:

$$(\\bigcup_i s_i) \\setminus t = \\bigcup_i (s_i \\setminus t)$$

In words: removing `t` from a union is the same as removing `t` from
each piece and then taking the union.

**Skills required** (all from Worlds 1–4):
- `ext` to start a set equality proof
- `constructor` to split the `↔`
- `obtain` to destructure set differences (`∧`) and existentials
- `rw [Set.mem_iUnion]` to convert `⋃` to `∃`
- `use` to provide witness indices
- Anonymous constructors `⟨_, _⟩` to build set differences

This is a long proof — take it one step at a time.
"

/-- Set difference distributes over indexed union. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) (t : Set α) :
    (⋃ i, s i) \ t = ⋃ i, (s i \ t) := by
  Hint "Start with `ext x` then `constructor`."
  ext x
  constructor
  -- Forward: x ∈ (⋃ i, s i) \ t → x ∈ ⋃ i, (s i \ t)
  · Hint "**Forward direction**: `x ∈ (⋃ i, s i) \\ t` means `x` is in the
    union AND not in `t`. Destructure, unpack the union, then rebuild."
    intro hx
    Hint "Use `obtain ⟨hu, hnt⟩ := hx` to get the two components."
    Hint (hidden := true) "Key move: `obtain` destructures the set difference,
    then `rw [Set.mem_iUnion]` converts the union to an existential."
    obtain ⟨hu, hnt⟩ := hx
    Hint "`hu : x ∈ ⋃ i, s i` and `hnt : x ∉ t`. Unpack the union."
    rw [Set.mem_iUnion] at hu
    Hint "Extract the witness index from `hu`."
    obtain ⟨i, hsi⟩ := hu
    Hint "You have `hsi : x ∈ s i` and `hnt : x ∉ t`. Build the goal:
    rewrite, provide the witness, and close."
    rw [Set.mem_iUnion]
    use i
    exact ⟨hsi, hnt⟩
  -- Backward: x ∈ ⋃ i, (s i \ t) → x ∈ (⋃ i, s i) \ t
  · Hint "**Backward direction**: `x ∈ ⋃ i, (s i \\ t)` means there exists
    an `i` where `x ∈ s i` and `x ∉ t`. Reconstruct the difference."
    intro hx
    Hint "Unpack the indexed union and destructure the difference."
    Hint (hidden := true) "Key move: `rw [Set.mem_iUnion] at hx` converts
    the union hypothesis to an existential, then `obtain` unpacks it."
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hsi, hnt⟩ := hx
    Hint "You have `hsi : x ∈ s i` and `hnt : x ∉ t`. Build
    `x ∈ (⋃ i, s i) \\ t` with `constructor`."
    constructor
    · Hint "Show `x ∈ ⋃ i, s i` by rewriting and providing the witness."
      rw [Set.mem_iUnion]
      exact ⟨i, hsi⟩
    · exact hnt

Conclusion "
You proved that set difference distributes over indexed union:
$(\\bigcup_i s_i) \\setminus t = \\bigcup_i (s_i \\setminus t)$

The proof integrated moves from all four worlds:

| Move | Source |
|---|---|
| `ext x` | Subset World |
| `obtain ⟨_, _⟩` | Set World |
| `constructor` | NNG4 baseline |
| `rw [Set.mem_iUnion]` | Indexed Ops World |
| `use i` | NNG4 baseline |
| `exact ⟨_, _⟩` | Set Ops World |
| Set difference reasoning | Set Ops World |

**One more level**: The boss awaits — a De Morgan law for indexed
unions that integrates `push_neg`, `mem_iInter`, and complement
reasoning.
"

/-- `Set.iUnion_diff` states `(⋃ i, t i) \\ s = ⋃ i, t i \\ s`. -/
TheoremDoc Set.iUnion_diff as "Set.iUnion_diff" in "Set"

/-- `iSup_sdiff_eq` is the lattice version: `(⨆ x, f x) \\ a = ⨆ x, f x \\ a`. -/
TheoremDoc iSup_sdiff_eq as "iSup_sdiff_eq" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iUnion_diff iSup_sdiff_eq
