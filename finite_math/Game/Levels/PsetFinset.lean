import Game.Levels.PsetFinset.L01_CompoundMembership
import Game.Levels.PsetFinset.L02_DoubleComplementSubset
import Game.Levels.PsetFinset.L03_FilterSubset
import Game.Levels.PsetFinset.L04_UnionSubset
import Game.Levels.PsetFinset.L05_UnionComplement
import Game.Levels.PsetFinset.L06_ImageNonempty
import Game.Levels.PsetFinset.L07_InjectiveNonMembership
import Game.Levels.PsetFinset.L08_FilterImageContainment
import Game.Levels.PsetFinset.L09_CardinalityRange
import Game.Levels.PsetFinset.L10_ImageUnionSdiff
import Game.Levels.PsetFinset.L11_DeMorganSubset
import Game.Levels.PsetFinset.L12_ImageMonotonicity
import Game.Levels.PsetFinset.L13_NonMembershipFromImage
import Game.Levels.PsetFinset.L14_Boss

World "PsetFinset"
Title "Problem Set: Finsets"

Introduction "
# Problem Set: Finsets

You've completed three lecture worlds on finsets:
- **FinsetBasics**: membership, range, insert, singleton, nonempty
- **FinsetOperations**: union, intersection, sdiff, filter, subset, ext, by_contra
- **FinsetImage**: image, forward/backward membership, cardinality, injectivity

Now apply these skills to **fresh problems** with sparser hints and
no new definitions. One new bridge fact — `Finset.card_range` —
connects range to cardinality.

**Note on disabled tactics**: `simp` is disabled throughout this
pset. Because `simp only` uses the same `simp` tactic internally,
it is also unavailable here. You learned `simp only` as a targeted
simplification tool in FinsetOperations — and it IS a good tool.
But this pset is specifically testing whether you can construct
`rw` chains from individual lemma names. The skill being assessed
is: given a membership goal, can you identify and apply the correct
sequence of `rw [Finset.mem_union]`, `rw [Finset.mem_inter]`, etc.
without automation choosing the lemmas for you? `simp only` will be
available again in later worlds. Tactics like `push_neg`, `linarith`,
and `tauto` are also disabled — you're expected to handle negations
with `by_contra` and `intro`, and arithmetic with `omega`.
"
