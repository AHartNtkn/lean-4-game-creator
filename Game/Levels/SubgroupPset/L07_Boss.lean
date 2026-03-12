import Game.Metadata

World "SubgroupPset"
Level 7

Title "Boss — When Intersection Equals a Factor"

Introduction
"
Prove that `H ⊓ K = H` if and only if `H ≤ K`. This connects
two perspectives on containment:

- `H ≤ K`: every element of `H` is in `K`
- `H ⊓ K = H`: intersecting with `K` doesn't shrink `H`

You'll need tools from across the world: `refine ⟨?_, ?_⟩`, `ext`,
`Subgroup.mem_inf`, and `≤` reasoning.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G) :
    H ⊓ K = H ↔ H ≤ K := by
  Hint "Start by splitting the `↔` with `refine ⟨?_, ?_⟩`."
  refine ⟨?_, ?_⟩
  · Hint "**Forward**: given `h : H ⊓ K = H`, show `H ≤ K`.

    Try `rw [← h]` — what does the goal become?"
    intro h
    Branch
      intro x hx
      Hint "You have `h : H ⊓ K = H` and `hx : {x} ∈ H`. Since
      `H ⊓ K = H`, try `rw [← h] at hx` to convert membership,
      then extract the `K`-component."
      rw [← h] at hx
      rw [Subgroup.mem_inf] at hx
      exact hx.2
    rw [← h]
    Hint "The goal is now `H ⊓ K ≤ K`. Extract the `K`-component
    from the intersection — you've done this before."
    intro x hx
    rw [Subgroup.mem_inf] at hx
    Hint (hidden := true) "`exact hx.2`"
    exact hx.2
  · Hint "**Backward**: given `hle : H ≤ K`, show `H ⊓ K = H`.

    Use `ext x` and split the `↔`."
    intro hle
    ext x
    refine ⟨?_, ?_⟩
    · Hint (hidden := true) "`intro hx; rw [Subgroup.mem_inf] at hx;
      exact hx.1`"
      intro hx
      rw [Subgroup.mem_inf] at hx
      exact hx.1
    · Hint "Given `{x} ∈ H`, show `{x} ∈ H ⊓ K`. Build the conjunction
      using `hle` for the `K`-component."
      intro hx
      rw [Subgroup.mem_inf]
      Hint (hidden := true) "`exact ⟨hx, hle hx⟩`"
      exact ⟨hx, hle hx⟩

Conclusion
"
Congratulations on completing the **Subgroup Problem Set**!

This result — `H ⊓ K = H ↔ H ≤ K` — characterizes containment in
terms of intersection: `H` is contained in `K` exactly when
intersecting with `K` doesn't shrink `H`.

The forward direction used a strategic rewrite: `rw [← h]` transformed
`H ≤ K` into `H ⊓ K ≤ K`, which you already knew how to prove from
Level 1. Recognizing that a rewrite can simplify a goal into something
you've already solved is a powerful technique.

On paper: *Forward: if `H ∩ K = H`, then for any `x ∈ H`, we have
`x ∈ H ∩ K` (since `H ∩ K = H`), so `x ∈ K`. Backward: if `H ≤ K`,
then `x ∈ H ∩ K` iff `x ∈ H ∧ x ∈ K` iff `x ∈ H` (the right-to-left
uses `H ≤ K`).*

You've now practiced every tool from the subgroup lectures:
- **Component-wise membership**: destructure `∧`, apply lemmas, rebuild
- **Containment chaining**: `≤` as function composition
- **Extensionality**: `ext` reduces equality to `↔` on elements
- **Membership triple**: `refine` to build a subgroup from scratch
- **Strategic rewriting**: use equalities of subgroups to transform goals

Looking ahead: in the next world, you'll prove the **center** of a
group is a subgroup — using the membership triple with a universal
quantifier. And the `ext` pattern will reappear when you prove that
an injective homomorphism has trivial kernel.
"
