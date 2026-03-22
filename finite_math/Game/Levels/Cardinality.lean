import Game.Levels.Cardinality.L01_WhatIsCardinality
import Game.Levels.Cardinality.L02_CardinalityOfSingleton
import Game.Levels.Cardinality.L03_NonemptyBridge
import Game.Levels.Cardinality.L04_NonemptyFromCard
import Game.Levels.Cardinality.L05_CardEqZero
import Game.Levels.Cardinality.L06_InsertAddsOne
import Game.Levels.Cardinality.L07_InsertIdempotency
import Game.Levels.Cardinality.L08_ConcreteCardinality
import Game.Levels.Cardinality.L09_RangeCardinality
import Game.Levels.Cardinality.L10_EraseRemovesOne
import Game.Levels.Cardinality.L11_SubsetsCantBeBigger
import Game.Levels.Cardinality.L12_CardFilterLe
import Game.Levels.Cardinality.L13_InclusionExclusion
import Game.Levels.Cardinality.L14_ConcreteInclusionExclusion
import Game.Levels.Cardinality.L15_DisjointUnion
import Game.Levels.Cardinality.L16_ComplementCounting
import Game.Levels.Cardinality.L17_InclusionExclusionDerivation
import Game.Levels.Cardinality.L18_MultiplicationPrinciple
import Game.Levels.Cardinality.L19_UnivFinset
import Game.Levels.Cardinality.L20_SubsetUniv
import Game.Levels.Cardinality.L21_ConcreteUniv
import Game.Levels.Cardinality.L22_AbstractPigeonhole
import Game.Levels.Cardinality.L23_GeneralPigeonhole
import Game.Levels.Cardinality.L24_Capstone
import Game.Levels.Cardinality.L25_SurjectiveImpliesInjective
import Game.Levels.Cardinality.L26_Boss

World "Cardinality"
Title "Cardinality"

Introduction "
# Cardinality: Counting Elements

You've been building finsets, proving membership, computing unions and
intersections, and mapping functions over them. But you haven't yet
asked: **how many elements does a finset contain?**

The answer is `Finset.card` — the cardinality function. For any finset
`s`, the expression `s.card` returns a natural number: the count of
elements in `s`.

This world covers the **card_* lemma family** — the toolkit for
computing and reasoning about cardinalities:

**Building up**:
- `card_empty`: $|\\emptyset| = 0$
- `card_singleton a`: $|\\{a\\}| = 1$
- `card_insert_of_notMem`: inserting a new element adds 1
- `card_range`: $|\\{0, \\ldots, n-1\\}| = n$

**Taking apart**:
- `card_erase_of_mem`: erasing an element subtracts 1

**Connecting**:
- `card_pos`: positive cardinality ↔ nonempty (both directions)
- `card_eq_zero`: zero cardinality ↔ empty

**Comparing**:
- `card_le_card`: subsets have smaller (or equal) cardinality

**Combining**:
- `card_union_add_card_inter`: the inclusion-exclusion formula
- `card_union_of_disjoint`: simplified form for disjoint sets
- `card_sdiff_add_card_inter`: complement counting
- `card_product`: the multiplication principle

**Deriving**:
- Why inclusion-exclusion holds — derived from disjoint union and
  complement counting

**Applying**:
- The **abstract pigeonhole principle** via cardinality — proving
  that more inputs than outputs forces a collision, without any
  case analysis
- The **capstone theorem**: for finite types, injective iff
  surjective — the mathematical climax of Phases 1-3

The proof pattern throughout: bring a card lemma into the context
with `have`, then use `omega` to handle the arithmetic.

You already met `Finset.card` and `card_image_le` in the Image world.
This world develops the full toolkit.
"
