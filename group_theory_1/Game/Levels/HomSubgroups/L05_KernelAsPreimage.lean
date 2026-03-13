import Game.Metadata

World "HomSubgroups"
Level 5

Title "Kernel and Range as Special Cases"

Introduction
"
The kernel and range are special cases of `comap` and `map`:

- `ker(f) = comap f ⊥` — the preimage of the trivial subgroup
- `range(f) = map f ⊤` — the image of the whole group

The first is true by definition — in Lean, `rfl` closes
`comap f ⊥ = f.ker`. We record it as `MonoidHom.comap_bot`.

The second requires a proof. Prove that `f.range = map f ⊤`.

Use `ext` to show two subgroups are equal by showing they have
the same elements.
"

/-- `MonoidHom.comap_bot` says:

`Subgroup.comap f ⊥ = f.ker`

The kernel is the preimage of the trivial subgroup.
This is true by definition. -/
TheoremDoc MonoidHom.comap_bot as "MonoidHom.comap_bot" in "Hom"

/-- `MonoidHom.range_eq_map` says:

`f.range = Subgroup.map f ⊤`

The range is the image of the whole group. -/
TheoremDoc MonoidHom.range_eq_map as "MonoidHom.range_eq_map" in "Hom"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem MonoidHom.range_eq_map

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) :
    f.range = Subgroup.map f ⊤ := by
  Hint "Two subgroups are equal when they have the same elements.
  Start with `ext y`."
  ext y
  Hint "The goal is `y ∈ f.range ↔ y ∈ Subgroup.map f ⊤`. Split
  the `↔` with `refine ⟨?_, ?_⟩`."
  refine ⟨?_, ?_⟩
  · -- Forward: y ∈ f.range → y ∈ map f ⊤
    Hint "Introduce the hypothesis: `intro hy`."
    intro hy
    Hint "Unfold range membership: `rw [MonoidHom.mem_range] at {hy}`."
    rw [MonoidHom.mem_range] at hy
    Hint "Now `{hy} : ∃ x, f x = y`. Unfold the goal:
    `rw [Subgroup.mem_map]`."
    rw [Subgroup.mem_map]
    Hint "The goal is `∃ x ∈ ⊤, f x = y`. Extract the witness
    from `{hy}`: `obtain ⟨x, hx⟩ := {hy}`."
    obtain ⟨x, hx⟩ := hy
    Hint (hidden := true) "Provide the witness with `⊤` membership:
    `exact ⟨x, Subgroup.mem_top x, hx⟩`."
    exact ⟨x, Subgroup.mem_top x, hx⟩
  · -- Backward: y ∈ map f ⊤ → y ∈ f.range
    Hint "Introduce the hypothesis: `intro hy`."
    intro hy
    Hint "Unfold image membership: `rw [Subgroup.mem_map] at {hy}`."
    rw [Subgroup.mem_map] at hy
    Hint "Now `{hy} : ∃ x ∈ ⊤, f x = y`. Unfold the goal:
    `rw [MonoidHom.mem_range]`."
    rw [MonoidHom.mem_range]
    Hint "Extract the witness: `obtain ⟨x, _, hx⟩ := {hy}`.

    The `_` discards the `x ∈ ⊤` component (which is always true)."
    obtain ⟨x, _, hx⟩ := hy
    Hint (hidden := true) "`exact ⟨x, hx⟩`."
    exact ⟨x, hx⟩

Conclusion
"
You proved `f.range = map f ⊤`: the range is the image of the
whole group.

The two bridge results connect your earlier tools to the new ones:

| Special case | General operation | Proof |
|-------------|-------------------|-------|
| `f.ker` | `comap f ⊥` | Definitional (`rfl`) |
| `f.range` | `map f ⊤` | By `ext` + witness shuffling |

The asymmetry is revealing: the preimage bridge is trivial (just
unfolding definitions), while the image bridge requires actual
witness manipulation. This reflects a general pattern — `comap`
is easier to reason about than `map` because membership is a
property check, not a witness production.

Notice also that `ker(g ∘ f) = comap f (ker g)` — the kernel of a
composition is the preimage of the outer map's kernel. In Lean,
this is definitionally true (`rfl` closes it): unfolding both
sides gives the same condition `g(f(x)) = 1`. This connects the
Composition world to the Preimage world.

We record this result as `MonoidHom.range_eq_map`.
"

NewTheorem MonoidHom.comap_bot MonoidHom.range_eq_map
