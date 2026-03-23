import Game.Levels.SetWorld.L01_WelcomeToSets
import Game.Levels.SetWorld.L02_SetBuilder
import Game.Levels.SetWorld.L03_NonMembership
import Game.Levels.SetWorld.L04_InfiniteSet
import Game.Levels.SetWorld.L05_NonMembershipExistential
import Game.Levels.SetWorld.L06_EmptySet
import Game.Levels.SetWorld.L07_UniversalSet
import Game.Levels.SetWorld.L08_CompoundPredicate
import Game.Levels.SetWorld.L09_Boss

World "SetWorld"
Title "Set World"

Introduction "
# Set World

Welcome to the first world of **Functions & Relations**!

In Lean 4, a set is not a primitive concept — it is built from
predicates. The definition is strikingly simple:

$$\\texttt{Set } \\alpha = \\alpha \\to \\texttt{Prop}$$

A set of natural numbers is just a function from natural numbers to
propositions. An element is *in* the set when the proposition it maps
to is true.

This means all set-theoretic reasoning reduces to propositional logic.
Membership is function application. The empty set uses `False`. The
universal set uses `True`. In this world, you will internalize this
reduction by working through concrete examples.

By the end of this world, you will be able to:
- Prove membership in sets defined by predicates
- Prove non-membership using negation
- Destructure existential witnesses with `obtain`
- Work with `Set.univ` and `∅`
- Handle compound predicates with logical connectives
- Recognize that set membership IS predicate evaluation

**Prerequisites**: You should be comfortable with `intro`, `exact`,
`constructor`, `use`, and `omega` from the Natural Number Game.

The boss at the end will ask you to combine all these moves on an
abstract predicate. Let's begin!
"
