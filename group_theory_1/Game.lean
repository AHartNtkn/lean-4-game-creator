import GameServer
import Game.Levels.GroupTutorial
import Game.Levels.GroupBasics
import Game.Levels.GroupBasicsPset
import Game.Levels.CommGroupIntro
import Game.Levels.SubgroupDef
import Game.Levels.SubgroupBasics
import Game.Levels.SubgroupPset
import Game.Levels.CenterIntro
import Game.Levels.CyclicGroups
import Game.Levels.HomDef
import Game.Levels.HomBasics
import Game.Levels.HomPset
import Game.Levels.HomComposition
import Game.Levels.HomSubgroups
import Game.Levels.CosetBasics
import Game.Levels.NormalDef
import Game.Levels.NormalPset

Title "Group Theory Game"
Introduction
"
Welcome to the **Group Theory Game**!

In this game, you'll learn group theory from the axioms through the
isomorphism theorems — by proving theorems in Lean 4 using Mathlib.

This is as much a tutorial on group theory as it is a guide to reasoning
about groups inside Mathlib.

We assume you know the basics of Lean's tactic mode (`rw`, `exact`, `intro`,
`apply`) from the Natural Number Game or similar. If not, we recommend
playing that first.

Click on a world to begin.
"

Info
"
## Group Theory Game

A lean4game for learning group theory with Mathlib.

**Prerequisites**: Basic Lean 4 tactic mode (e.g., from the Natural Number Game).

**Topics covered**:
- Group axioms and basic properties
- Commutative and additive groups
- Subgroups and the center
- Group homomorphisms, kernels, and images
- Normal subgroups and quotient groups
- The isomorphism theorems
"

Languages "en"
CaptionShort "Group Theory"
CaptionLong "Learn group theory from axioms to isomorphism theorems using Lean 4 and Mathlib."

Dependency GroupTutorial → GroupBasics
Dependency GroupBasics → GroupBasicsPset
Dependency GroupBasics → CommGroupIntro
Dependency GroupBasicsPset → SubgroupDef
Dependency CommGroupIntro → SubgroupDef
Dependency SubgroupDef → SubgroupBasics
Dependency SubgroupBasics → SubgroupPset
Dependency SubgroupPset → CenterIntro
Dependency CommGroupIntro → CenterIntro
Dependency SubgroupBasics → CyclicGroups
Dependency SubgroupPset → HomDef
Dependency HomDef → HomBasics
Dependency HomBasics → HomPset
Dependency HomBasics → HomComposition
Dependency HomComposition → HomSubgroups
Dependency SubgroupBasics → HomSubgroups
Dependency SubgroupPset → CosetBasics
Dependency CosetBasics → NormalDef
Dependency HomBasics → NormalDef
Dependency NormalDef → NormalPset

MakeGame
