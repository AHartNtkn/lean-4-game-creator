import Game.Metadata

World "SetOpsWorld"
Level 9

Title "Complement Law"

Introduction "
# s ∩ sᶜ = ∅

The most fundamental fact about complements is that a set and its
complement have **no elements in common**:

$$s \\cap s^c = \\emptyset$$

This makes sense: `x ∈ s ∩ sᶜ` means `x ∈ s` AND `x ∉ s`, which is
a contradiction. So no element can belong to both.

**Proving a set equals ∅**: Use `ext x` to reduce to
`x ∈ s ∩ sᶜ ↔ x ∈ ∅`. Since `x ∈ ∅` is definitionally `False`,
the forward direction asks you to derive a contradiction from
`x ∈ s ∩ sᶜ`, and the backward direction asks you to prove anything
from `False`.

**Proof plan**:
1. `ext x` then `constructor`
2. **Forward**: `intro hx`, then `obtain ⟨hs, hns⟩ := hx` to get
   `hs : x ∈ s` and `hns : x ∉ s`. Apply `hns` to `hs`.
3. **Backward**: `intro hx` — but `hx : False`, so use `exact hx.elim`.
"

/-- A set and its complement have empty intersection. -/
Statement (α : Type) (s : Set α) : s ∩ sᶜ = ∅ := by
  Hint "Use `ext x` to reduce the set equality to a membership
  biconditional, then `constructor` to split the `↔`."
  ext x
  constructor
  -- Forward: x ∈ s ∩ sᶜ → x ∈ ∅ (i.e., → False)
  · Hint "Given `x ∈ s ∩ sᶜ`, derive `False`. Start with `intro hx`,
    then use `obtain ⟨hs, hns⟩ := hx` to extract both components."
    intro hx
    Hint "Use `obtain ⟨hs, hns⟩ := hx` to get `hs : x ∈ s` and
    `hns : x ∈ sᶜ` (which is `x ∉ s`, i.e., `x ∈ s → False`)."
    Hint (hidden := true) "`obtain ⟨hs, hns⟩ := hx` then
    `exact hns hs` — applying the negation `hns` to `hs` gives `False`."
    obtain ⟨hs, hns⟩ := hx
    Hint "`hs : x ∈ s` and `hns : x ∈ sᶜ` (= `x ∉ s` = `x ∈ s → False`).
    These contradict: `exact hns hs`."
    Branch
      contradiction
    exact hns hs
  -- Backward: x ∈ ∅ → x ∈ s ∩ sᶜ (i.e., False → anything)
  · Hint "The hypothesis says `x ∈ ∅`, which is `False`. From `False`,
    anything follows. Use `intro hx` then `exact hx.elim`."
    Hint (hidden := true) "`intro hx` then `exact hx.elim`.

    (`False.elim` proves anything from a proof of `False`.)"
    intro hx
    Hint "`hx : False` (since `x ∈ ∅` is definitionally `False`).
    Use `exact hx.elim` — `False.elim` proves any proposition from
    `False`. Alternatively, `contradiction` also works here."
    exact hx.elim

Conclusion "
You proved `s ∩ sᶜ = ∅` — a set and its complement are disjoint.

This level introduced two new proof shapes:

1. **Contradiction from `∩` and `ᶜ`**: When you have both `x ∈ s`
   and `x ∉ s`, apply the negation to derive `False`:
   `exact hns hs`.

2. **Proving from `∅` membership**: Since `x ∈ ∅` is `False`, and
   `False` implies anything, use `exact hx.elim` (or `contradiction`).

This proof used the **standard proof pattern for set equalities**:
`ext x`, then `constructor`, then prove each direction at the element
level. You will see this pattern many times — it is THE way to prove
that two sets are equal.

The companion identity `s ∪ sᶜ = Set.univ` (every element is in `s`
or its complement) is also true but requires classical reasoning
(the law of excluded middle). You will prove it later in this world
once you learn `by_contra`.

The library name is `Set.inter_compl_self`.
"

/-- `Set.inter_compl_self` states `s ∩ sᶜ = ∅`. -/
TheoremDoc Set.inter_compl_self as "Set.inter_compl_self" in "Set"

/-- `Set.compl_inter_self` states `sᶜ ∩ s = ∅`. -/
TheoremDoc Set.compl_inter_self as "Set.compl_inter_self" in "Set"

/-- `inf_compl_eq_bot` is the lattice version: `a ⊓ aᶜ = ⊥`. -/
TheoremDoc inf_compl_eq_bot as "inf_compl_eq_bot" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.inter_compl_self Set.compl_inter_self inf_compl_eq_bot
