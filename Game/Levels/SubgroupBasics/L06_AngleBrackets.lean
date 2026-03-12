import Game.Metadata

World "SubgroupBasics"
Level 6

Title "Building Conjunctions"

Introduction
"
In the last level, you extracted one half of a conjunction using `.1`.
Now you'll go the other direction: given two membership proofs,
*build* a conjunction to show something belongs to an intersection.

If you have `hH : a ∈ H` and `hK : a ∈ K`, you can build a proof
of `a ∈ H ∧ a ∈ K` with **angle brackets**:

`exact ⟨hH, hK⟩`

The angle brackets `⟨⟩` are typed `\\<` and `\\>`. They build a
value of a structure type (here `And`) from its components.

Prove that `a` belongs to `H ⊓ K`.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H K : Subgroup G)
    (a : G) (hH : a ∈ H) (hK : a ∈ K) : a ∈ H ⊓ K := by
  Hint "The goal is `a ∈ H ⊓ K`. Rewrite it with
  `rw [Subgroup.mem_inf]` to get `a ∈ H ∧ a ∈ K`, then build the
  conjunction: `exact ⟨hH, hK⟩`.

  The angle brackets `⟨⟩` are typed `\\<` and `\\>`."
  rw [Subgroup.mem_inf]
  Hint "Now the goal is `a ∈ H ∧ a ∈ K`. Build the conjunction
  with `exact ⟨hH, hK⟩`."
  exact ⟨hH, hK⟩

Conclusion
"
Angle brackets `⟨⟩` are the dual of `.1` and `.2`:

- **Destructuring**: `h.1` and `h.2` extract parts of `h : P ∧ Q`
- **Constructing**: `⟨hp, hq⟩` builds a proof of `P ∧ Q`

You'll use both constantly. In the next level, you'll learn a tactic
that makes destructuring even cleaner.
"
