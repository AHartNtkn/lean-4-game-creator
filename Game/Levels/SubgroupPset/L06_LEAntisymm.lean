import Game.Metadata

World "SubgroupPset"
Level 6

Title "Antisymmetry of Containment"

Introduction
"
If `H ≤ K` and `K ≤ H`, then `H = K`. Two subgroups containing
each other must be equal. Prove it.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G)
    (hHK : H ≤ K) (hKH : K ≤ H) : H = K := by
  Hint "Reduce the equality to element-wise membership with `ext x`,
  then split the `↔` and use the two containment hypotheses."
  ext x
  refine ⟨?_, ?_⟩
  · Hint (hidden := true) "`intro hx; exact hHK hx`"
    intro hx
    exact hHK hx
  · Hint (hidden := true) "`intro hx; exact hKH hx`"
    intro hx
    exact hKH hx

Conclusion
"
This result — `H ≤ K → K ≤ H → H = K` — is **antisymmetry** of the
subgroup ordering, sometimes called `le_antisymm`. Together with
reflexivity (`H ≤ H`, which is just `intro x hx; exact hx`) and
transitivity (Level 3), this makes `≤` a *partial order* on subgroups.

On paper: *To show `H = K`, take any `x`. If `x ∈ H`, then `x ∈ K`
since `H ≤ K`. If `x ∈ K`, then `x ∈ H` since `K ≤ H`. Hence `H`
and `K` have the same elements and are equal.*
"
