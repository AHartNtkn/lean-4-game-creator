import Game.Metadata

World "SetOpsWorld"
Level 15

Title "Complement Union Law"

Introduction "
# s ∪ sᶜ = Set.univ

Back in Level 9, you proved `s ∩ sᶜ = ∅` — a set and its complement
are disjoint. We mentioned that the companion identity
`s ∪ sᶜ = Set.univ` also holds but requires classical reasoning.

Now you have that technique: `by_contra` + `push_neg`. Time to fulfill
the promise.

$$s \\cup s^c = \\text{univ}$$

Every element belongs to `s` or to `sᶜ` — there is no third option.
This is the **law of excluded middle** applied to set membership.

**Proof plan**:
1. `ext x`, `constructor`
2. **Forward** (`→`): `x ∈ s ∪ sᶜ → x ∈ Set.univ`. Since
   `x ∈ Set.univ` unfolds to `True`, use `intro _` then `constructor`
   (which closes any `True` goal).
3. **Backward** (`←`): `x ∈ Set.univ → x ∈ s ∪ sᶜ`. This is the
   interesting direction. You need `x ∈ s ∨ x ∉ s` but cannot choose
   a side without more information. Use `by_contra h`, then
   `change` + `push_neg at h` to convert `¬(x ∈ s ∨ x ∉ s)` to
   `x ∉ s ∧ x ∈ s` — a direct contradiction.
"

/-- Every element is in s or in the complement of s. -/
Statement (α : Type) (s : Set α) : s ∪ sᶜ = Set.univ := by
  Hint "Use `ext x` to reduce to membership, then `constructor`."
  ext x
  constructor
  -- Forward: s ∪ sᶜ → Set.univ (trivial)
  · Hint "`x ∈ Set.univ` is definitionally `True`. After `intro _`,
    close the goal with `constructor` (which proves `True`)."
    Hint (hidden := true) "`intro _` then `constructor`."
    intro _
    constructor
  -- Backward: Set.univ → s ∪ sᶜ (requires classical reasoning)
  · Hint "The interesting direction: given `x ∈ Set.univ` (which is just
    `True`), prove `x ∈ s ∪ sᶜ`, i.e., `x ∈ s ∨ x ∉ s`.

    You cannot choose `left` or `right` without knowing whether `x ∈ s`.
    Use `by_contra h` to assume the goal is false."
    intro _
    Hint "The goal is `x ∈ s ∪ sᶜ`, which is `x ∈ s ∨ x ∉ s`. Use
    `by_contra h` to assume `¬(x ∈ s ∨ x ∉ s)` and derive `False`."
    Hint (hidden := true) "`by_contra h` then
    `change ¬(x ∈ s ∨ x ∉ s) at h` then `push_neg at h` then
    `exact h.1 h.2`."
    by_contra h
    Hint "`h` says the goal is false. Use
    `change ¬(x ∈ s ∨ x ∉ s) at h` to make the logical form explicit."
    change ¬(x ∈ s ∨ x ∉ s) at h
    Hint "Now use `push_neg at h` to push the negation through the
    disjunction."
    push_neg at h
    Hint "`push_neg` converted `¬(x ∈ s ∨ x ∉ s)` to `x ∉ s ∧ x ∈ s`.
    So `h.1 : x ∉ s` (= `x ∈ s → False`) and `h.2 : x ∈ s`.
    These contradict: `exact h.1 h.2`."
    exact h.1 h.2

Conclusion "
You proved `s ∪ sᶜ = Set.univ` — every element is in `s` or its
complement. This is the **law of excluded middle** for sets.

Together with Level 9, you now have both complement laws:

| Identity | Meaning | Classical? |
|---|---|---|
| `s ∩ sᶜ = ∅` | No element is in both | No (constructive) |
| `s ∪ sᶜ = Set.univ` | Every element is in one | Yes (`by_contra`) |

The asymmetry is revealing: proving that `s` and `sᶜ` are *disjoint*
requires no classical reasoning, but proving they *cover everything*
does. This is because the first only says \"having both leads to
contradiction,\" while the second says \"one must hold\" — and asserting
existence without construction is exactly what classical logic adds.

The library name is `Set.union_compl_self`.
"

/-- `Set.union_compl_self` states `s ∪ sᶜ = Set.univ`. -/
TheoremDoc Set.union_compl_self as "Set.union_compl_self" in "Set"

/-- `sup_compl_eq_top` is the lattice version: `a ⊔ aᶜ = ⊤`. -/
TheoremDoc sup_compl_eq_top as "sup_compl_eq_top" in "Set"

NewTheorem Set.union_compl_self

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.union_compl_self sup_compl_eq_top Set.compl_union_self compl_sup_eq_top
