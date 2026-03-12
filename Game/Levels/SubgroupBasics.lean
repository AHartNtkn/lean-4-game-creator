import Game.Levels.SubgroupBasics.L01_SubgroupLE
import Game.Levels.SubgroupBasics.L02_MemBot
import Game.Levels.SubgroupBasics.L03_LETop
import Game.Levels.SubgroupBasics.L04_BotLE
import Game.Levels.SubgroupBasics.L05_MemInf
import Game.Levels.SubgroupBasics.L06_AngleBrackets
import Game.Levels.SubgroupBasics.L07_ObtainTactic
import Game.Levels.SubgroupBasics.L08_ObtainPractice
import Game.Levels.SubgroupBasics.L09_ExtTactic
import Game.Levels.SubgroupBasics.L10_InfComm
import Game.Levels.SubgroupBasics.L11_Boss

World "SubgroupBasics"
Title "Subgroup Basics"

Introduction
"
Welcome to **Subgroup Basics**, where you'll explore how subgroups
relate to each other.

In the previous world, you learned to *build* individual subgroups by
verifying three closure properties. Now the question is: given two
subgroups `H` and `K` of the same group `G`, what structure do they
form?

The answer is a **lattice** — a partially ordered set with meets and
joins. The key operations are:

- **Containment**: `H ≤ K` means every element of `H` is also in `K`
- **Bottom**: `⊥` is the trivial subgroup `{1}` — the smallest subgroup
- **Top**: `⊤` is the whole group `G` — the largest subgroup
- **Meet (intersection)**: `H ⊓ K` is the largest subgroup contained
  in both `H` and `K`

For any subgroup `H`, we always have `⊥ ≤ H ≤ ⊤`.

You'll also learn two new tactics: `obtain` for breaking apart
conjunction hypotheses (`∧`), and `ext` for proving two subgroups
are equal by checking element-wise membership.

By the boss level, you'll build an intersection subgroup from scratch
— proving all three closure properties using the membership-triple
technique from the last world, combined with the new ability to
destructure `∧` hypotheses.
"
