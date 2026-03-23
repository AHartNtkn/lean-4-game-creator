import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 23

Title "Boss: Indexed Union Distributes over Intersection"

Introduction "
# Boss: Distributivity for Indexed Unions

In Set Operations World, you proved the **distributive law** for binary
operations: $s \\cap (t \\cup u) = (s \\cap t) \\cup (s \\cap u)$. Now prove
the indexed generalization:

$$(\\bigcup_i s_i) \\cap t = \\bigcup_i (s_i \\cap t)$$

This says: being in some `s i` AND in `t` is the same as being in
some `s i ∩ t`.

**Skills required** (all taught in this world and earlier):
- `ext` to start a set equality proof (Subset World)
- `constructor` to split the `↔` (NNG4-baseline)
- `obtain` to destructure `∩` hypotheses (Subset World)
- `rw [Set.mem_iUnion]` to handle indexed unions (this world)
- `obtain` to destructure `∃` (Set World)
- `use` to provide witness indices (this world)

**Proof plan**: The proof has two directions. In each direction, you
will need to unpack an indexed union (getting an `∃`), destructure
an intersection (getting an `∧`), and rebuild the other side.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂ Set.mem_prod Set.mem_powerset_iff
NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset
TheoremTab "Set"

/-- Indexed union distributes over intersection. -/
Statement (α : Type) (ι : Type) (s : ι → Set α) (t : Set α) :
    (⋃ i, s i) ∩ t = ⋃ i, (s i ∩ t) := by
  Hint "Start with `ext x` to reduce to a membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔` into forward and backward
  directions."
  constructor
  -- Forward: x ∈ (⋃ i, s i) ∩ t → x ∈ ⋃ i, (s i ∩ t)
  · Hint "**Forward direction**: Assume `x ∈ (⋃ i, s i) ∩ t` and prove
    `x ∈ ⋃ i, (s i ∩ t)`.

    Start with `intro hx`, then destructure the intersection:
    `obtain ⟨hu, ht⟩ := hx`."
    intro hx
    Hint "Destructure the intersection: `obtain ⟨hu, ht⟩ := hx` gives
    you `hu : x ∈ ⋃ i, s i` and `ht : x ∈ t`."
    obtain ⟨hu, ht⟩ := hx
    Hint "Now unpack the indexed union in `hu`:
    `rw [Set.mem_iUnion] at hu`."
    Hint (hidden := true) "`rw [Set.mem_iUnion] at hu` converts `hu`
    to `∃ i, x ∈ s i`. Then `obtain ⟨i, hsi⟩ := hu` to get the
    witness. Then `rw [Set.mem_iUnion]` on the goal, `use i`, and
    `exact ⟨hsi, ht⟩`."
    rw [Set.mem_iUnion] at hu
    Hint "Now `hu : ∃ i, x ∈ s i`. Extract the witness:
    `obtain ⟨i, hsi⟩ := hu`."
    obtain ⟨i, hsi⟩ := hu
    Hint "You have `hsi : x ∈ s i` and `ht : x ∈ t`. The goal is
    `x ∈ ⋃ i, (s i ∩ t)`. Rewrite with `rw [Set.mem_iUnion]`, then
    `use i` to provide the witness index."
    rw [Set.mem_iUnion]
    use i
    Hint "The goal is `x ∈ s i ∩ t`, which is a conjunction. Build it
    with `exact ⟨hsi, ht⟩` or use `constructor`."
    exact ⟨hsi, ht⟩
  -- Backward: x ∈ ⋃ i, (s i ∩ t) → x ∈ (⋃ i, s i) ∩ t
  · Hint "**Backward direction**: Assume `x ∈ ⋃ i, (s i ∩ t)` and prove
    `x ∈ (⋃ i, s i) ∩ t`.

    Start with `intro hx`, then unpack the indexed union:
    `rw [Set.mem_iUnion] at hx`."
    intro hx
    Hint "Unpack the union: `rw [Set.mem_iUnion] at hx`."
    rw [Set.mem_iUnion] at hx
    Hint "Now `hx : ∃ i, x ∈ s i ∩ t`. Extract the witness and
    destructure the intersection in one step:
    `obtain ⟨i, hsi, ht⟩ := hx`."
    Hint (hidden := true) "`obtain ⟨i, hsi, ht⟩ := hx` gives
    `i : ι`, `hsi : x ∈ s i`, `ht : x ∈ t`. Then build the goal
    with `constructor`, `rw [Set.mem_iUnion]` + `exact ⟨i, hsi⟩`
    for the first part, and `exact ht` for the second."
    obtain ⟨i, hsi, ht⟩ := hx
    Hint "You have `hsi : x ∈ s i` and `ht : x ∈ t`. The goal is
    `x ∈ (⋃ i, s i) ∩ t`. Use `constructor` to split into two parts."
    constructor
    · Hint "Prove `x ∈ ⋃ i, s i`. Rewrite and provide the witness."
      Hint (hidden := true) "`rw [Set.mem_iUnion]` then `exact ⟨i, hsi⟩`."
      rw [Set.mem_iUnion]
      exact ⟨i, hsi⟩
    · Hint "`ht` is exactly what you need."
      exact ht

Conclusion "
Congratulations — you have completed **Indexed Operations World**!

You proved that indexed unions distribute over intersection:
$(\\bigcup_i s_i) \\cap t = \\bigcup_i (s_i \\cap t)$

This is the same *extract-transform-repack* pattern from Level 5
(monotonicity of indexed union), now with an intersection layer added.
In each direction, you extracted data from the hypothesis, transformed
it (regrouping the intersection and union membership), and repacked it
into the goal.

The proof integrated every major skill from this world:

| Move | Where used |
|---|---|
| `ext x` | start the set equality |
| `constructor` | split `↔` and `∩` |
| `obtain` | destructure `∩` and `∃` |
| `rw [Set.mem_iUnion]` | convert `⋃` to `∃` |
| `use i` | provide witness index |
| `exact` | close goals |

**Recap of this world**:

| Construction | Notation | Meaning | Key lemma |
|---|---|---|---|
| Indexed union | `⋃ i, s i` | `∃ i, x ∈ s i` | `Set.mem_iUnion` |
| Indexed intersection | `⋂ i, s i` | `∀ i, x ∈ s i` | `Set.mem_iInter` |
| Bounded union | `⋃ i ∈ t, s i` | `∃ i ∈ t, x ∈ s i` | `Set.mem_iUnion₂` |
| Bounded intersection | `⋂ i ∈ t, s i` | `∀ i ∈ t, x ∈ s i` | `Set.mem_iInter₂` |
| Cartesian product | `s ×ˢ t` | `p.1 ∈ s ∧ p.2 ∈ t` | `Set.mem_prod` |
| Nonemptiness | `Set.Nonempty s` | `∃ x, x ∈ s` | — |
| Powerset | `𝒫 s` | `t ⊆ s` | `Set.mem_powerset_iff` |

Together with Level 22, you proved both distributive laws:

| Law | Statement |
|---|---|
| Level 22 | $(\\bigcap_i s_i) \\cup t = \\bigcap_i (s_i \\cup t)$ |
| This level | $(\\bigcup_i s_i) \\cap t = \\bigcup_i (s_i \\cap t)$ |

**The pattern persists**: Every set construction reduces to a logical
statement. Indexed unions and intersections are the quantifier versions
of binary union and intersection. Cartesian products are conjunctions
of pair components. Powerset membership is subset.

**A note on naming**: In Lean's Mathlib library, `⋃` and `⋂` are
special cases of a general lattice structure where `⋃ = iSup` and
`⋂ = iInf`. That is why you sometimes see `iSup` and `iInf` in
theorem names (like the disabled `iSup_inf_eq`).

**Looking ahead**: Indexed unions will be essential when studying
images and preimages of functions. For example, images distribute
over unions: $f(\\bigcup_i s_i) = \\bigcup_i f(s_i)$ — a fact whose
proof uses exactly the skills you just practiced.

But first: a problem set that will test all the set theory you have
learned so far — membership, subsets, set operations, and indexed
operations — on fresh problems with less scaffolding.
"

/-- `Set.iUnion_inter` states `(⋃ i, t i) ∩ s = ⋃ i, t i ∩ s`. -/
TheoremDoc Set.iUnion_inter as "Set.iUnion_inter" in "Set"

/-- `Set.inter_iUnion` states `s ∩ ⋃ i, t i = ⋃ i, s ∩ t i`. -/
TheoremDoc Set.inter_iUnion as "Set.inter_iUnion" in "Set"

/-- `iSup_inf_eq` is the lattice version of indexed union/intersection
distributivity. -/
TheoremDoc iSup_inf_eq as "iSup_inf_eq" in "Set"

/-- `inf_iSup_eq` is the lattice version (commuted order). -/
TheoremDoc inf_iSup_eq as "inf_iSup_eq" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iUnion_inter Set.inter_iUnion iSup_inf_eq inf_iSup_eq
