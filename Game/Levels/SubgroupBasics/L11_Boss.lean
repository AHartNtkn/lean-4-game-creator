import Game.Metadata

World "SubgroupBasics"
Level 11

Title "Boss — The Intersection Subgroup"

Introduction
"
Time to put it all together. Given two subgroups `H` and `K` of `G`,
construct the **intersection subgroup** from scratch — a `Subgroup G`
whose carrier is `{g | g ∈ H ∧ g ∈ K}`.

Use `apply Subgroup.mk_carrier` as in the previous world, but with
a twist: the carrier predicate involves `∧`, so each closure proof
starts by destructuring the conjunction hypotheses using `obtain`.

Your toolkit for this level:

| Theorem | Statement |
|---------|-----------|
| `one_mem H` | `1 ∈ H` |
| `mul_mem` | `x ∈ H → y ∈ H → x * y ∈ H` |
| `inv_mem` | `x ∈ H → x⁻¹ ∈ H` |

| Tactic | Use |
|--------|-----|
| `Subgroup.mk_carrier` | Set up the subgroup with `apply` |
| `intro` | Introduce elements and hypotheses |
| `show` | Unfold membership (optional) |
| `obtain ⟨_, _⟩` | Destructure `∧` hypotheses |
| `exact ⟨_, _⟩` | Build `∧` goals |
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G) :
    ∃ S : Subgroup G, S.carrier = {g : G | g ∈ H ∧ g ∈ K} := by
  Hint "Start with `apply Subgroup.mk_carrier` to set up the three
  closure obligations."
  apply Subgroup.mk_carrier
  · Hint "**mul_mem**: If `x` and `y` are both in `H` and `K`,
    then `x * y` is too.

    Start with `intro x y hx hy`."
    intro x y hx hy
    Hint "You have `hx : {x} ∈ H ∧ {x} ∈ K` and
    `hy : {y} ∈ H ∧ {y} ∈ K`. Use `obtain` to split each one:

    `obtain ⟨hxH, hxK⟩ := hx`
    `obtain ⟨hyH, hyK⟩ := hy`"
    obtain ⟨hxH, hxK⟩ := hx
    obtain ⟨hyH, hyK⟩ := hy
    Hint "Now build the conjunction: `{x} * {y} ∈ H` (from `mul_mem`)
    and `{x} * {y} ∈ K` (from `mul_mem`).

    `exact ⟨mul_mem hxH hyH, mul_mem hxK hyK⟩`"
    exact ⟨mul_mem hxH hyH, mul_mem hxK hyK⟩
  · Hint "**one_mem**: Show `1 ∈ H ∧ 1 ∈ K`.

    Both halves follow from `one_mem`."
    Hint (hidden := true) "`exact ⟨one_mem H, one_mem K⟩`"
    exact ⟨one_mem H, one_mem K⟩
  · Hint "**inv_mem**: If `x` is in both `H` and `K`, then `x⁻¹`
    is too.

    `intro x hx` then `obtain ⟨hxH, hxK⟩ := hx`."
    intro x hx
    obtain ⟨hxH, hxK⟩ := hx
    Hint (hidden := true) "`exact ⟨inv_mem hxH, inv_mem hxK⟩`"
    exact ⟨inv_mem hxH, inv_mem hxK⟩

Conclusion
"
Congratulations on completing **Subgroup Basics**!

You built the intersection of two subgroups from scratch, proving all
three closure properties. Each closure proof followed the same pattern:

1. **Destructure** the `∧` hypothesis with `obtain ⟨_, _⟩`
2. **Apply** the membership lemma (`one_mem`, `mul_mem`, `inv_mem`)
   to each component separately
3. **Rebuild** the conjunction with `exact ⟨_, _⟩`

This is the **component-wise membership** pattern: when the carrier
involves `∧`, prove each part independently and recombine. You'll
see it again whenever intersections or conjunctive conditions appear.

On paper, the `mul_mem` proof would read: *\"Let `x, y ∈ H ∩ K`.
Then `x, y ∈ H` and `x, y ∈ K`. Since `H` is a subgroup, `xy ∈ H`.
Since `K` is a subgroup, `xy ∈ K`. Hence `xy ∈ H ∩ K`.\"* The
`obtain` steps correspond to \"Then `x, y ∈ H` and `x, y ∈ K`\", and
the angle-bracket rebuild corresponds to \"Hence `xy ∈ H ∩ K`\".

Your new tools from this world:

| Item | Type |
|------|------|
| `H ≤ K` | Subgroup containment |
| `⊥` | Trivial subgroup `{1}` |
| `⊤` | Whole group |
| `H ⊓ K` | Intersection of subgroups |
| `Subgroup.mem_bot` | `x ∈ ⊥ ↔ x = 1` |
| `Subgroup.mem_top` | `x ∈ ⊤` (always true) |
| `Subgroup.mem_inf` | `x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K` |
| `obtain` | Destructure `∧` and `∃` hypotheses |
| `ext` | Prove subgroup equality by membership |
| `refine` | Partially fill in terms with `?_` placeholders |

Looking ahead: the **center** of a group — the set of elements
commuting with everything — is a subgroup you can locate in this
lattice. And the question \"is the kernel equal to `⊥`?\" will
characterize injective homomorphisms. The lattice isn't just
abstract structure — it's the language for the major theorems ahead.

In the next world, you'll practice these tools on varied examples.
"
