import Game.Levels.GroupTutorial.L01_RightIdentity
import Game.Levels.GroupTutorial.L02_LeftIdentity
import Game.Levels.GroupTutorial.L03_RightInverse
import Game.Levels.GroupTutorial.L04_LeftInverse
import Game.Levels.GroupTutorial.L05_Associativity
import Game.Levels.GroupTutorial.L06_CalcBlocks
import Game.Levels.GroupTutorial.L07_TargetedRewriting
import Game.Levels.GroupTutorial.L08_Boss

World "GroupTutorial"
Title "The Group Axioms"

Introduction
"
Welcome to your first world: **The Group Tutorial**.

A **group** is a set $G$ with a binary operation $*$, an identity element $1$,
and an inverse operation $\\cdot^{-1}$. Groups capture the idea of reversible
transformations — rotations of a shape, permutations of a list, symmetries
of a molecule.

A group must satisfy three axioms:

1. **Associativity**: $(a * b) * c = a * (b * c)$
2. **Right identity**: $a * 1 = a$
3. **Right inverse**: $a * a^{-1} = 1$

From these three, two useful consequences follow automatically:

4. **Left identity**: $1 * a = a$
5. **Left inverse**: $a^{-1} * a = 1$

We'll use all five as tools in this world. In the next world, you'll see
why (4) and (5) follow from (1)–(3).

In Lean and Mathlib, these are the theorems `mul_assoc`, `mul_one`, `one_mul`,
`mul_inv_cancel`, and `inv_mul_cancel`.

In this world, you'll learn to use each axiom one at a time, then combine them
in multi-step proofs using `calc` blocks.

**Your goal**: by Level 8, you'll prove from these five axioms alone that

$(a * b) \\cdot (b^{-1} * a^{-1}) = 1$

**Notation warning**: In Lean, multiplication is *left-associated*. That means
`a * b * c` is the same as `(a * b) * c`, **not** `a * (b * c)`. You'll need
`mul_assoc` to move the parentheses.

You already know `rw` and `exact` from the Natural Number Game. Those are the
only tactics you need here — plus a new one called `calc` that you'll meet in
Level 6.

Let's begin.
"
