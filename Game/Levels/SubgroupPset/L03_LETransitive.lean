import Game.Metadata

World "SubgroupPset"
Level 3

Title "Subgroup Containment Is Transitive"

Introduction
"
If `H ≤ K` and `K ≤ L`, then `H ≤ L`. The math is immediate, but
the Lean proof exercises a useful pattern: chaining function
applications.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K L : Subgroup G)
    (hHK : H ≤ K) (hKL : K ≤ L) : H ≤ L := by
  Hint "Unfold what `H ≤ L` means with `intro x hx`, then chain
  the two containment hypotheses."
  intro x hx
  Branch
    apply hKL
    Hint "The goal is `{x} ∈ K`. You have `hHK : H ≤ K` and
    `hx : {x} ∈ H`. Apply `hHK` to `hx`."
    exact hHK hx
  Hint (hidden := true) "`exact hKL (hHK hx)`"
  exact hKL (hHK hx)

Conclusion
"
Transitivity of `≤` means the subgroup ordering is a *partial order*
(reflexive, transitive, antisymmetric). Reflexivity (`H ≤ H`) follows
immediately from `intro x hx; exact hx`. Together with the boss's
antisymmetry proof, these three properties make `≤` a genuine partial
order on the subgroup lattice.

Notice the proof is pure function composition: `hKL (hHK hx)`.
On paper: *If `x ∈ H`, then `x ∈ K` (since `H ≤ K`), then `x ∈ L`
(since `K ≤ L`).*

This is what `≤` being defined as `∀ x, x ∈ H → x ∈ K` buys you:
containment proofs reduce to applying hypotheses.
"
