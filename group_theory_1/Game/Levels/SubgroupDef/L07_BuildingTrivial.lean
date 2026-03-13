import Game.Metadata

World "SubgroupDef"
Level 7

Title "Building the Trivial Subgroup"

Introduction
"
Now for the real challenge of this world: **building** a subgroup
from scratch, with a specific carrier set.

The goal uses `∃ H : Subgroup G, H.carrier = {g | ...}` — this
means 'produce a subgroup whose carrier is this specific set.'
You can't just produce any subgroup; it must have the right carrier.

The theorem `Subgroup.mk_carrier` does the heavy lifting. After
`apply Subgroup.mk_carrier`, the goal splits into **three** concrete
proof obligations — one for each closure property:

1. **mul_mem**: if `a ∈ S` and `b ∈ S`, then `a * b ∈ S`
2. **one_mem**: `1 ∈ S`
3. **inv_mem**: if `x ∈ S`, then `x⁻¹ ∈ S`

Use `·` to focus on each goal, then `intro` to introduce hypotheses
and `show` to unfold the set membership into a concrete equation.

Start with the simplest possible subgroup: the **trivial subgroup**
`{1}`, the set containing only the identity element.
"

/-- `Subgroup.mk_carrier` builds a subgroup with a specified carrier.

After `apply Subgroup.mk_carrier`, the goal splits into three:
- `mul_mem`: `∀ a b, a ∈ S → b ∈ S → a * b ∈ S`
- `one_mem`: `1 ∈ S`
- `inv_mem`: `∀ x, x ∈ S → x⁻¹ ∈ S`

This is the standard way to construct a specific subgroup in
tactic mode. Each obligation is a short, focused proof. -/
TheoremDoc Subgroup.mk_carrier as "Subgroup.mk_carrier" in "Subgroup"

/-- `rfl` closes a goal of the form `x = x` — it proves that
anything equals itself.

You can use `rfl` as a standalone tactic or write `exact rfl` — both
work identically. Use it when the goal is a trivially true equality
like `1 = 1` or `a = a`. -/
TacticDoc rfl

/-- `inv_one` says `(1 : G)⁻¹ = 1` — the inverse of the identity is
the identity.

Use it with `rw [inv_one]` to simplify `1⁻¹` to `1`. -/
TheoremDoc inv_one as "inv_one" in "Group"

NewTactic rfl
NewTheorem Subgroup.mk_carrier inv_one

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] :
    ∃ H : Subgroup G, H.carrier = {g : G | g = 1} := by
  Hint "Use `apply Subgroup.mk_carrier` to set up the three closure
  obligations."
  apply Subgroup.mk_carrier
  · Hint "**mul_mem**: If `a` and `b` are in the carrier
    (i.e., `a = 1` and `b = 1`), show `a * b` is too.

    Start with `intro a b ha hb`."
    intro a b ha hb
    Hint "Use `show` to unfold the membership into an equation, then
    rewrite using `ha` and `hb`."
    Hint (hidden := true) "`show a * b = 1` then `rw [ha, hb, one_mul]`"
    show a * b = 1
    rw [ha, hb, one_mul]
  · Hint "**one_mem**: Show `1` is in the carrier.

    `show (1 : G) = 1` to unfold, then `rfl`."
    show (1 : G) = 1
    rfl
  · Hint "**inv_mem**: If `x` is in the carrier, then `x⁻¹` is too.

    Start with `intro x hx`."
    intro x hx
    Hint "Use `show` to unfold membership, then rewrite.

    The theorem `inv_one` says `(1 : G)⁻¹ = 1`."
    Hint (hidden := true) "`show x⁻¹ = 1` then `rw [hx, inv_one]`"
    show x⁻¹ = 1
    rw [hx, inv_one]

Conclusion
"
You just built a subgroup from scratch! The **trivial subgroup**
`{1}` is the smallest possible subgroup of any group.

The construction pattern you used will appear in every subgroup
construction:

1. `apply Subgroup.mk_carrier` — creates three obligations
2. For each obligation: `intro` the hypotheses, `show` to unfold
   membership, then prove the mathematical claim.

The trivial subgroup was easy because the carrier predicate (`g = 1`)
is very restrictive — there's only one element to worry about.

In the next levels, you'll build subgroups with more interesting
carriers, where the closure proofs require real group algebra.
"
