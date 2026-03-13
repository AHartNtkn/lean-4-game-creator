import Game.Metadata

World "SubgroupPset"
Level 5

Title "A Different Carrier"

Introduction
"
Build a subgroup from scratch — but this time the carrier is
`{g : G | g⁻¹ ∈ H}`.

Same `apply Subgroup.mk_carrier` pattern as before. The twist: think
about what each obligation asks after you unfold the carrier predicate
with `show`. You'll need `inv_one`, `mul_inv_rev`, and `inv_mem` —
tools from earlier worlds appearing in a new context.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) :
    ∃ S : Subgroup G, S.carrier = {g : G | g⁻¹ ∈ H} := by
  Hint "Start with `apply Subgroup.mk_carrier` to set up the three
  closure obligations."
  apply Subgroup.mk_carrier
  · Hint "**mul_mem**: You need `(x * y)⁻¹ ∈ H`. Use `show` to
    see the unfolded goal. What does `mul_inv_rev` tell you about
    `(x * y)⁻¹`?"
    intro x y hx hy
    show (x * y)⁻¹ ∈ H
    Hint (hidden := true) "`rw [mul_inv_rev]; exact mul_mem hy hx`
    — note the swapped order!"
    rw [mul_inv_rev]
    exact mul_mem hy hx
  · Hint "**one_mem**: What is `(1 : G)⁻¹`?"
    show (1 : G)⁻¹ ∈ H
    Hint (hidden := true) "`rw [inv_one]; exact one_mem H`"
    rw [inv_one]
    exact one_mem H
  · Hint "**inv_mem**: You have `x⁻¹ ∈ H` and need `(x⁻¹)⁻¹ ∈ H`.
    Which membership lemma gives this directly?"
    intro x hx
    show (x⁻¹)⁻¹ ∈ H
    Hint (hidden := true) "`exact inv_mem hx`"
    exact inv_mem hx

Conclusion
"
This subgroup is actually equal to `H` — since `H` is closed under
inverses, `g⁻¹ ∈ H` if and only if `g ∈ H`. The point was the
*proof exercise*: the same `apply Subgroup.mk_carrier` pattern works
regardless of the carrier's surface form.

Notice how `mul_inv_rev` (shoes-and-socks from the Group Basics world)
appeared naturally in `mul_mem` — proof moves transfer across worlds.
Also notice the order swap: `mul_mem hy hx` instead of `mul_mem hx hy`,
because `(x * y)⁻¹ = y⁻¹ * x⁻¹` reverses the factors.
"
