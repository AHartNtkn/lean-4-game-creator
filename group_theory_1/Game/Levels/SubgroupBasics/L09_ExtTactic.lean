import Game.Metadata

World "SubgroupBasics"
Level 9

Title "Subgroup Extensionality"

Introduction
"
How do you prove two subgroups are equal? The **extensionality**
principle says: two subgroups with the same elements are equal.

The `ext` tactic implements this. If the goal is `H = K` for
subgroups `H K : Subgroup G`, then `ext x` reduces it to:

`x ∈ H ↔ x ∈ K`

An `↔` (if and only if) goal has two directions. You can split it
with `refine ⟨?_, ?_⟩` — the same angle-bracket syntax you already
know, but now for `↔` instead of `∧`. This creates two goals:
- Forward: `x ∈ H → x ∈ K`
- Backward: `x ∈ K → x ∈ H`

Then use `intro` to introduce the hypothesis and prove each direction.

Prove that `H ⊓ ⊤ = H` — intersecting with the whole group changes
nothing.
"

/-- The `refine` tactic is like `exact`, but allows `?_` placeholders
for parts you want to prove later.

For example, `refine ⟨?_, ?_⟩` on an `↔` goal creates two subgoals:
one for each direction. Each `?_` becomes a new goal to prove.

Use `refine` whenever you want to provide part of a proof term and
leave holes for the rest. -/
TacticDoc refine

/-- The `ext` tactic proves two structures are equal by showing they
agree on all components.

For subgroups, `ext x` reduces `H = K` to `x ∈ H ↔ x ∈ K`.

This is the **extensionality principle**: subgroups with the same
elements are equal.

After `ext x`, split the `↔` with `refine ⟨?_, ?_⟩`, then prove
each direction with `intro` and membership reasoning. -/
TacticDoc ext

NewTactic ext refine

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) : H ⊓ ⊤ = H := by
  Hint "Use `ext x` to reduce the equality to element-wise membership."
  ext x
  Hint "The goal is `{x} ∈ H ⊓ ⊤ ↔ {x} ∈ H`. Split the `↔` with
  `refine ⟨?_, ?_⟩` to get two subgoals: one for each direction."
  refine ⟨?_, ?_⟩
  · Hint "**Forward**: given `{x} ∈ H ⊓ ⊤`, show `{x} ∈ H`.

    Use `intro hx` to get the hypothesis, then
    `rw [Subgroup.mem_inf] at hx` and `obtain ⟨hH, _⟩ := hx` to
    extract the `H`-membership."
    intro hx
    rw [Subgroup.mem_inf] at hx
    Hint (hidden := true) "`obtain ⟨hH, hTop⟩ := hx` then `exact hH`."
    obtain ⟨hH, _⟩ := hx
    exact hH
  · Hint "**Backward**: given `{x} ∈ H`, show `{x} ∈ H ⊓ ⊤`.

    Use `intro hx`, then `rw [Subgroup.mem_inf]` to convert the goal
    to a conjunction. Build it with `exact ⟨hx, Subgroup.mem_top {x}⟩`."
    intro hx
    Hint (hidden := true) "`rw [Subgroup.mem_inf]` then
    `exact ⟨hx, Subgroup.mem_top {x}⟩`."
    rw [Subgroup.mem_inf]
    exact ⟨hx, Subgroup.mem_top x⟩

Conclusion
"
The `ext` tactic is the standard way to prove subgroup equality. The
full pattern is:

1. `ext x` — reduce to membership
2. `refine ⟨?_, ?_⟩` — split the `↔` into two directions
3. `intro` + prove each direction

This **extensionality principle** — structures are equal when they
have the same elements — will appear again for kernels, images, and
quotient groups in later worlds.

On paper, this proof reads: *\"To show `H ⊓ ⊤ = H`, we check
`x ∈ H ⊓ ⊤` iff `x ∈ H`. Forward: if `x ∈ H ⊓ ⊤`, then `x ∈ H`
and `x ∈ ⊤`; in particular `x ∈ H`. Backward: if `x ∈ H`, then
`x ∈ H` and `x ∈ ⊤` (trivially), so `x ∈ H ⊓ ⊤`.\"*
"
