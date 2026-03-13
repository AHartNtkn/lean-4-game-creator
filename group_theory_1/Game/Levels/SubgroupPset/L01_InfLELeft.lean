import Game.Metadata

World "SubgroupPset"
Level 1

Title "Intersection Is Below Both"

Introduction
"
The intersection `H ⊓ K` contains exactly the elements in both `H`
and `K`. Can you prove it's contained in `H`?

Unpack the intersection membership, then extract the `H`-component.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G) : H ⊓ K ≤ H := by
  Hint "The goal `H ⊓ K ≤ H` means `∀ x, x ∈ H ⊓ K → x ∈ H`.
  Start with `intro x hx`, then unpack `hx` using `Subgroup.mem_inf`
  and extract the `H`-component."
  intro x hx
  rw [Subgroup.mem_inf] at hx
  Hint (hidden := true) "`obtain ⟨hH, _⟩ := hx` then `exact hH`.
  Or simply `exact hx.1`."
  obtain ⟨hH, _⟩ := hx
  exact hH

Conclusion
"
This is half of what makes `⊓` the *greatest lower bound*: the
intersection sits below both `H` and `K`. The other half (`H ⊓ K ≤ K`)
follows by the same argument, extracting `.2` instead of `.1`.

On paper: *If `x ∈ H ∩ K`, then `x ∈ H` and `x ∈ K`; in particular
`x ∈ H`.*
"
