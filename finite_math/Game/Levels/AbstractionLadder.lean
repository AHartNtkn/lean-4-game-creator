import Game.Levels.AbstractionLadder.L01_MeetTheList
import Game.Levels.AbstractionLadder.L02_ListsAreOrdered
import Game.Levels.AbstractionLadder.L03_ListMembership
import Game.Levels.AbstractionLadder.L04_AppendLength
import Game.Levels.AbstractionLadder.L05_DuplicateElements
import Game.Levels.AbstractionLadder.L06_Permutations
import Game.Levels.AbstractionLadder.L07_PermChain
import Game.Levels.AbstractionLadder.L08_PermLengthExercise
import Game.Levels.AbstractionLadder.L09_MeetTheMultiset
import Game.Levels.AbstractionLadder.L10_MultisetCount
import Game.Levels.AbstractionLadder.L11_MultisetCardinality
import Game.Levels.AbstractionLadder.L12_NodupSingleton
import Game.Levels.AbstractionLadder.L13_NodupDistinct
import Game.Levels.AbstractionLadder.L14_ToFinset
import Game.Levels.AbstractionLadder.L15_MultisetToFinset
import Game.Levels.AbstractionLadder.L16_PermToFinset
import Game.Levels.AbstractionLadder.L17_NodupCardEqualsLength
import Game.Levels.AbstractionLadder.L18_DedupDemonstration
import Game.Levels.AbstractionLadder.L19_ContrastLevel
import Game.Levels.AbstractionLadder.L20_PrimeFactorsGrounding
import Game.Levels.AbstractionLadder.L21_PermNodupCoaching
import Game.Levels.AbstractionLadder.L22_DescentPayoff
import Game.Levels.AbstractionLadder.L23_Boss

World "AbstractionLadder"
Title "Abstraction Ladder"

Introduction "
# The Abstraction Ladder: List → Multiset → Finset

You've spent several worlds working with `Finset` — but where do
finsets come from? What are they *made of*?

The answer is a three-layer **abstraction ladder**:

```
   Finset α     ← no duplicates, no order
      ↑ (dedup)
   Multiset α   ← no order, keeps duplicates
      ↑ (quotient by permutation)
   List α       ← ordered, keeps duplicates
```

Each step up the ladder **forgets** something:
- **List → Multiset** forgets *order* by identifying lists that are
  permutations of each other
- **Multiset → Finset** forgets *duplicates* by deduplication

This world climbs the ladder from the bottom. You'll learn:
- What lists are and how they work (length, membership, append)
- Why order matters for lists (and why we need permutations)
- What permutations are and how to build them (swap, cons, trans)
- How multisets arise as quotients of lists by permutation
- How `Nodup` (no duplicates) is the bridge to finsets
- How `List.toFinset` and `Multiset.toFinset` climb the ladder
- How cardinality changes (or doesn't) at each layer

Understanding the ladder gives you power: when a finset proof is hard,
you can descend to the list or multiset level, use richer tools there,
and bring the result back up.
"
