import Game.Metadata

World "SetOpsWorld"
Level 16

Title "Boss: Distributivity"

Introduction "
# Boss: Intersection Distributes over Union

Time to integrate everything. Prove the **distributive law** for sets:

$$s \\cap (t \\cup u) = (s \\cap t) \\cup (s \\cap u)$$

This says: being in `s` AND in `t ∪ u` is the same as being in
`s ∩ t` OR in `s ∩ u`. It is the set-theoretic version of the
propositional identity $P \\land (Q \\lor R) \\iff (P \\land Q) \\lor (P \\land R)$.

**Skills required** (all taught in this world):
- `ext` to start a set equality proof
- `constructor` to split the `↔`
- `obtain` to destructure `∩` hypotheses
- `cases ... with | inl ... | inr ...` to split `∪` hypotheses
- `left` / `right` to build `∪` goals
- `constructor` again to build `∩` goals

The proof has two directions. Each direction requires destructuring
one side and building the other. There are no new tricks — just the
moves you have practiced. Take it one step at a time.
"

/-- Intersection distributes over union. -/
Statement (α : Type) (s t u : Set α) :
    s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  Hint "Start with `ext x` to reduce to a membership biconditional."
  Branch
    -- Antisymm path
    apply Set.Subset.antisymm
    · Hint "Prove `s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)`. Start with
      `intro x hx` then destructure `hx`."
      intro x hx
      obtain ⟨hs, htu⟩ := hx
      cases htu with
      | inl ht =>
        left
        constructor
        · exact hs
        · exact ht
      | inr hu =>
        right
        constructor
        · exact hs
        · exact hu
    · intro x hx
      cases hx with
      | inl hst =>
        obtain ⟨hs, ht⟩ := hst
        constructor
        · exact hs
        · left
          exact ht
      | inr hsu =>
        obtain ⟨hs, hu⟩ := hsu
        constructor
        · exact hs
        · right
          exact hu
  ext x
  Hint "Use `constructor` to split the `↔` into two directions."
  constructor
  -- Forward: s ∩ (t ∪ u) → (s ∩ t) ∪ (s ∩ u)
  · Hint "**Forward direction**: Given `x ∈ s ∩ (t ∪ u)`, prove
    `x ∈ (s ∩ t) ∪ (s ∩ u)`.

    Start with `intro hx`, then destructure the intersection:
    `obtain ⟨hs, htu⟩ := hx`."
    intro hx
    Hint "Destructure `hx` with `obtain ⟨hs, htu⟩ := hx` to get
    `hs : x ∈ s` and `htu : x ∈ t ∪ u`."
    Hint (hidden := true) "`obtain ⟨hs, htu⟩ := hx` then
    `cases htu with | inl ht | inr hu`.

    In each case, use `left`/`right` + `constructor` + `exact`."
    obtain ⟨hs, htu⟩ := hx
    Hint "Now `hs : x ∈ s` and `htu : x ∈ t ∪ u`. Case-split on the
    union: `cases htu with | inl ht | inr hu`."
    cases htu with
    | inl ht =>
      Hint "`ht : x ∈ t` and `hs : x ∈ s`. You need
      `x ∈ (s ∩ t) ∪ (s ∩ u)`. Since `x ∈ s` and `x ∈ t`, the
      element is in `s ∩ t`, so use `left` to select the left
      side of the union."
      Hint (hidden := true) "`left` then `constructor` then
      `· exact hs` and `· exact ht`."
      left
      constructor
      · exact hs
      · exact ht
    | inr hu =>
      Hint "`hu : x ∈ u` and `hs : x ∈ s`. The element is in
      `s ∩ u`, so use `right`."
      Hint (hidden := true) "`right` then `constructor` then
      `· exact hs` and `· exact hu`."
      right
      constructor
      · exact hs
      · exact hu
  -- Backward: (s ∩ t) ∪ (s ∩ u) → s ∩ (t ∪ u)
  · Hint "**Backward direction**: Given `x ∈ (s ∩ t) ∪ (s ∩ u)`,
    prove `x ∈ s ∩ (t ∪ u)`.

    Start with `intro hx`, then case-split on the union:
    `cases hx with | inl hst | inr hsu`."
    intro hx
    Hint "Split the union hypothesis: `cases hx with | inl hst | inr hsu`."
    Hint (hidden := true) "`cases hx with | inl hst | inr hsu`.

    In each case, destructure the intersection, then build
    `s ∩ (t ∪ u)` with `constructor`."
    cases hx with
    | inl hst =>
      Hint "`hst : x ∈ s ∩ t`. Destructure with
      `obtain ⟨hs, ht⟩ := hst`."
      obtain ⟨hs, ht⟩ := hst
      Hint "Build `x ∈ s ∩ (t ∪ u)` with `constructor`. The first
      part is `x ∈ s` (from `hs`). The second part is `x ∈ t ∪ u` —
      use `left` since `x ∈ t`."
      Hint (hidden := true) "`constructor` then `· exact hs` then
      `· left` and `  exact ht`."
      constructor
      · exact hs
      · left
        exact ht
    | inr hsu =>
      Hint "`hsu : x ∈ s ∩ u`. Destructure with
      `obtain ⟨hs, hu⟩ := hsu`."
      obtain ⟨hs, hu⟩ := hsu
      Hint "Build `x ∈ s ∩ (t ∪ u)` with `constructor`. Use `right`
      for the union part since `x ∈ u`."
      Hint (hidden := true) "`constructor` then `· exact hs` then
      `· right` and `  exact hu`."
      constructor
      · exact hs
      · right
        exact hu

Conclusion "
Congratulations — you have completed **Set Operations World**!

You proved the distributive law by working through every step
of the propositional logic underlying the set operations:

| Set Operation | Logic | Proving | Using |
|---|---|---|---|
| `∪` (union) | `∨` (or) | `left`/`right` | `cases h with \\| inl \\| inr` |
| `∩` (intersection) | `∧` (and) | `constructor` | `.1`/`.2` or `obtain` |
| `ᶜ` (complement) | `¬` (not) | `intro h` | apply `h` |
| `\\` (difference) | `∧ ¬` | `constructor` | `.1`/`.2` or `obtain` |

**The central pattern**: Every set-theoretic proof is a logical proof
in disguise. To prove a set identity, use `ext` to reduce to
membership, then work purely in propositional logic.

Additional tools and results from this world:
- `push_neg` — pushes negation through connectives
- `by_contra` — proof by contradiction (classical reasoning)
- `cases h with | inl ... | inr ...` — case analysis on disjunctions
- De Morgan: `(s ∪ t)ᶜ = sᶜ ∩ tᶜ` and `(s ∩ t)ᶜ = sᶜ ∪ tᶜ`
- Complement laws: `s ∩ sᶜ = ∅` and `s ∪ sᶜ = Set.univ`
- Double complement: `sᶜᶜ = s`
- Distributivity: `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`

**Challenge**: The *dual* distributive law `s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u)`
also holds. Its proof uses the same techniques — try it on paper!

**Looking ahead**: The binary operations `∪` and `∩` generalize to
indexed versions `⋃` and `⋂`. The pattern is the same: binary `∨`
generalizes to `∃` over an index, and binary `∧` generalizes to `∀`.
You will see this in the next world.

Later, you will explore how these operations interact with functions.
Preimages preserve all operations — `f⁻¹(s ∪ t) = f⁻¹(s) ∪ f⁻¹(t)`
and similarly for `∩` and `ᶜ`. But images only preserve union:
`f(s ∩ t) ⊆ f(s) ∩ f(t)` is merely a subset, not an equality in
general. This asymmetry between images and preimages will be a central
theme of later worlds.
"

/-- `Set.inter_union_distrib_left` states `s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u`. -/
TheoremDoc Set.inter_union_distrib_left as "Set.inter_union_distrib_left" in "Set"

/-- `inf_sup_left` is the lattice version: `a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c`. -/
TheoremDoc inf_sup_left as "inf_sup_left" in "Set"

/-- `Set.union_inter_distrib_right` is the dual distributivity law. -/
TheoremDoc Set.union_inter_distrib_right as "Set.union_inter_distrib_right" in "Set"

/-- `sup_inf_right` is the lattice version of the dual distributivity. -/
TheoremDoc sup_inf_right as "sup_inf_right" in "Set"

/-- `Set.inter_distrib_left` is an alias for `Set.inter_union_distrib_left`. -/
TheoremDoc Set.inter_distrib_left as "Set.inter_distrib_left" in "Set"

/-- `and_or_left` states `a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c`. -/
TheoremDoc and_or_left as "and_or_left" in "Set"

/-- `and_or_right` states `(a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c`. -/
TheoremDoc and_or_right as "and_or_right" in "Set"

/-- `or_and_left` states `a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c)`. -/
TheoremDoc or_and_left as "or_and_left" in "Set"

/-- `or_and_right` states `a ∧ b ∨ c ↔ (a ∨ c) ∧ (b ∨ c)`. -/
TheoremDoc or_and_right as "or_and_right" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.inter_union_distrib_left inf_sup_left Set.union_inter_distrib_right sup_inf_right Set.inter_distrib_left and_or_left and_or_right or_and_left or_and_right
