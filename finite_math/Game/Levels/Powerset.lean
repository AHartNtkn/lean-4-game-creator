import Game.Levels.Powerset.L01_EmptyInPowerset
import Game.Levels.Powerset.L02_SelfMembership
import Game.Levels.Powerset.L03_ConcretePowerset
import Game.Levels.Powerset.L04_SubsetImpliesMember
import Game.Levels.Powerset.L05_MemberImpliesSubset
import Game.Levels.Powerset.L06_PowersetMonotonicity
import Game.Levels.Powerset.L07_PowersetMonoConverse
import Game.Levels.Powerset.L08_PowersetMonoIff
import Game.Levels.Powerset.L09_ComplementInPowerset
import Game.Levels.Powerset.L10_ComplementCard
import Game.Levels.Powerset.L11_ComplementInvolution
import Game.Levels.Powerset.L12_CardPowerset
import Game.Levels.Powerset.L13_PowersetEmptySet
import Game.Levels.Powerset.L14_SingletonPowerset
import Game.Levels.Powerset.L15_MeetPowersetCard
import Game.Levels.Powerset.L16_PowersetCardExtract
import Game.Levels.Powerset.L17_CardPowersetCard
import Game.Levels.Powerset.L18_ConcretePowersetCard
import Game.Levels.Powerset.L19_ZeroElementSubsets
import Game.Levels.Powerset.L20_PowersetCardZero
import Game.Levels.Powerset.L21_SingletonSubsets
import Game.Levels.Powerset.L22_FullSetSubset
import Game.Levels.Powerset.L23_TooManyElements
import Game.Levels.Powerset.L24_SubsetBound
import Game.Levels.Powerset.L25_ConcreteCount
import Game.Levels.Powerset.L26_ChooseSymmCoaching
import Game.Levels.Powerset.L27_Boss

World "Powerset"
Title "Powerset"

Introduction "
# Powerset: All Subsets of a Set

Given a finite set $s$, how many subsets does it have? What if you only
want subsets of a specific size?

**Concrete motivation**: Imagine choosing toppings for a pizza from a
menu of $n$ items. Each topping is independently *in* or *out* — that
gives $2^n$ possible pizzas. If you want exactly $k$ toppings, there
are $\\binom{n}{k}$ options. The powerset formalizes this: it is the
collection of all possible choices.

The **powerset** $\\mathcal{P}(s)$ is the collection of all subsets of $s$.
The key characterization: $t \\in \\mathcal{P}(s)$ if and only if $t \\subseteq s$.

In this world you'll learn:

- **`Finset.powerset`** and its membership lemma `mem_powerset`
- **`Finset.card_powerset`**: a set with $n$ elements has $2^n$ subsets
- **`Finset.powersetCard k s`**: the subsets of `s` with exactly $k$ elements
- **`Finset.card_powersetCard`**: the count of $k$-element subsets is $\\binom{n}{k}$

This connects the *set-theoretic* operation (listing subsets) to the
*combinatorial* numbers (binomial coefficients) that you studied in the
BinomialCoefficients world. There, $\\binom{n}{k}$ was defined recursively
via Pascal's identity. Here, you'll see its **counting meaning**: it counts
the $k$-element subsets.

**Prerequisites**: `mem_powerset` for subset reasoning, `card_le_card` from
Cardinality, and `Nat.choose` identities from BinomialCoefficients.
"
