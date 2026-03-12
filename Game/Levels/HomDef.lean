import Game.Levels.HomDef.L01_SimpTactic
import Game.Levels.HomDef.L02_DirectedSimp
import Game.Levels.HomDef.L03_WhatIsAHom
import Game.Levels.HomDef.L04_MapOne
import Game.Levels.HomDef.L05_MapInv
import Game.Levels.HomDef.L06_SimpWithHoms
import Game.Levels.HomDef.L07_BuildAHom
import Game.Levels.HomDef.L08_Boss

World "HomDef"
Title "Homomorphisms"
Introduction
"
Welcome to **Homomorphisms** — the study of structure-preserving maps
between groups.

A **group homomorphism** is a function `f : G → H` between groups that
respects multiplication:

`f(a · b) = f(a) · f(b)` for all `a, b ∈ G`

This single condition — preserving multiplication — forces `f` to
preserve everything else: the identity (`f(1) = 1`) and inverses
(`f(a⁻¹) = f(a)⁻¹`). You'll prove both of these consequences.

In Lean 4 + Mathlib, group homomorphisms use the type `MonoidHom` with
notation `G →* H`. Don't be confused by the name — `MonoidHom` is used
for group homomorphisms too, because groups are monoids. There is no
separate `GroupHom` type.

⚠️ **Notation warning**: `→*` is the homomorphism arrow, not `→`
(plain function arrow). When you see `f : G →* H`, you know `f` carries
the `map_mul` property automatically.

Before we meet homomorphisms, we'll learn a new tool: the `simp` tactic,
which automates routine algebraic simplification. You'll use `simp`
extensively when working with homomorphisms.

By the boss level, you'll construct a homomorphism from scratch and
prove that if `f(a) = f(b)`, then `f(a · b⁻¹) = 1` — the first glimpse
of what will become **kernel reasoning** in the next world.
"
