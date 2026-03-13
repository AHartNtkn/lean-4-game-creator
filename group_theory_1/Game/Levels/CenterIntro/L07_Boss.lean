import Game.Metadata

World "CenterIntro"
Level 7

Title "Boss — Center Characterizes Commutativity"

Introduction
"
Prove the full characterization: the center of a group is the whole
group if and only if every pair of elements commutes.

`center G = ⊤ ↔ ∀ x y : G, x * y = y * x`

Both directions have been proved separately in Levels 5 and 6. Now
combine them using `refine ⟨?_, ?_⟩` to split the `↔`.

Your toolkit:

| Tool | Purpose |
|------|---------|
| `refine ⟨?_, ?_⟩` | Split `↔` into two goals |
| `Subgroup.eq_top_iff'` | `H = ⊤ ↔ ∀ x, x ∈ H` |
| `Subgroup.mem_center_iff` | `z ∈ center G ↔ ∀ g, g * z = z * g` |
| `apply ... .mp` | Reduce commutativity to center membership |
| `intro` | Introduce hypotheses and ∀-variables |

Note: the forward direction uses `[Group G]`, not `[CommGroup G]`.
You don't have `mul_comm` available — instead, you extract
commutativity from the hypothesis that `center G = ⊤`.
"

/-- `center_eq_top_iff_forall_comm` says:

`Subgroup.center G = ⊤ ↔ ∀ x y : G, x * y = y * x`

A group is abelian if and only if its center is the whole group. -/
TheoremDoc center_eq_top_iff_forall_comm as "center_eq_top_iff_forall_comm" in "Center"

TheoremTab "Center"

DisabledTactic group

Statement center_eq_top_iff_forall_comm (G : Type*) [Group G] :
    Subgroup.center G = ⊤ ↔ ∀ x y : G, x * y = y * x := by
  Hint "Split the `↔` with `refine ⟨?_, ?_⟩`."
  refine ⟨?_, ?_⟩
  · Hint "**Forward**: `center G = ⊤ → ∀ x y, x * y = y * x`.

    Same proof as Level 6.
    Start with `intro h` then `rw [Subgroup.eq_top_iff'] at h`."
    intro h
    rw [Subgroup.eq_top_iff'] at h
    Hint "Now `intro x y` to introduce the elements."
    intro x y
    Hint "Use `apply Subgroup.mem_center_iff.mp` to reduce the goal
    to a center membership, then close with `exact h y`."
    Branch
      exact Subgroup.mem_center_iff.mp (h y) x
    apply Subgroup.mem_center_iff.mp
    Hint (hidden := true) "`exact h y`"
    exact h y
  · Hint "**Backward**: `(∀ x y, x * y = y * x) → center G = ⊤`.

    Same proof as Level 5.
    Start with `intro h` then `rw [Subgroup.eq_top_iff']`."
    intro h
    Branch
      ext z
      refine ⟨?_, ?_⟩
      · intro _
        exact Subgroup.mem_top z
      · intro _
        rw [Subgroup.mem_center_iff]
        intro g
        exact h g z
    rw [Subgroup.eq_top_iff']
    Hint "Now `intro z` and show `z ∈ center G`."
    intro z
    rw [Subgroup.mem_center_iff]
    Hint "The goal is `∀ (g : G), g * {z} = {z} * g`. Introduce `g`
    and use `h`."
    intro g
    Hint (hidden := true) "`exact h g {z}`"
    exact h g z

Conclusion
"
Congratulations on completing **The Center**!

You proved that a group is abelian if and only if its center is the
whole group:

`center G = ⊤ ↔ ∀ x y : G, x * y = y * x`

Both directions used the same two tools — `Subgroup.eq_top_iff'` and
`Subgroup.mem_center_iff` — in opposite order:
- **Forward**: `eq_top_iff'` extracts universal membership from the
  hypothesis, then `apply mem_center_iff.mp` reduces commutativity
  to center membership.
- **Backward**: `eq_top_iff'` reduces the goal to universal membership,
  then `rw [mem_center_iff]` reduces each membership to commutativity.

The center Z(G) measures the distance from abelianness:
- `Z(G) = ⊤` means fully commutative
- `Z(G) = ⊥` means only `1` commutes with everything (\"centerless\")
- In between, `Z(G)` captures the abelian core

On paper: *\"Z(G) = G iff ∀ x, y: xy = yx. Forward: if Z(G) = G,
every y ∈ Z(G), so xy = yx. Backward: if xy = yx for all x, y,
then every z commutes with all g, so z ∈ Z(G).\"*

Your new tools from this world:

| Item | Type | Purpose |
|------|------|---------|
| `Subgroup.center G` | Definition | The center (elements commuting with everything) |
| `Subgroup.mem_center_iff` | Theorem | `z ∈ center G ↔ ∀ g, g * z = z * g` |
| `Subgroup.eq_top_iff'` | Theorem | `H = ⊤ ↔ ∀ x, x ∈ H` |

Notice the asymmetry: Level 5 used `[CommGroup G]`, so `mul_comm`
was an axiom. Here both directions used only `[Group G]` — you
extracted commutativity from the hypothesis instead. A `CommGroup`
is exactly a `Group` where `∀ x y, x * y = y * x` holds by
definition. What you proved is: the center characterizes exactly
when this extra axiom holds.

The center will appear again: it is always a **normal** subgroup
(the proof is immediate — if `z` commutes with `g`, then
`g * z * g⁻¹ = z`), and the center of a **p-group** is always
non-trivial (a key step in classifying finite groups).
"
