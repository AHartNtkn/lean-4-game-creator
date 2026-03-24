import GameServer.Commands

import Game.Levels.SetWorld
import Game.Levels.SubsetWorld
import Game.Levels.SetOpsWorld
import Game.Levels.IndexedOpsWorld
import Game.Levels.PsetSets
import Game.Levels.PreimageWorld

Title "Functions & Relations"
Introduction
"
# Functions & Relations

Functions, Relations, Equivalences, and Encodability

This course is under construction.
"

-- Phase 1: Sets and Logic
-- SetWorld has no dependencies (first world)
-- SubsetWorld depends on SetWorld (W01 → W02)
-- SetOpsWorld depends on SetWorld and SubsetWorld (W01, W02 → W03)
-- IndexedOpsWorld depends on SetWorld, SubsetWorld, and SetOpsWorld (W01, W02, W03 → W04)
-- PsetSets depends on all four lecture worlds (W01, W02, W03, W04 → W05)
Dependency SetWorld → SubsetWorld
Dependency SetWorld → SetOpsWorld
Dependency SubsetWorld → SetOpsWorld
Dependency SetWorld → IndexedOpsWorld
Dependency SubsetWorld → IndexedOpsWorld
Dependency SetOpsWorld → IndexedOpsWorld
Dependency SetWorld → PsetSets
Dependency SubsetWorld → PsetSets
Dependency SetOpsWorld → PsetSets
Dependency IndexedOpsWorld → PsetSets

-- Phase 2: Images and Preimages
-- PreimageWorld depends on SetWorld, SubsetWorld, SetOpsWorld, and IndexedOpsWorld (W01, W02, W03, W04 → W06)
Dependency SetWorld → PreimageWorld
Dependency SubsetWorld → PreimageWorld
Dependency SetOpsWorld → PreimageWorld
Dependency IndexedOpsWorld → PreimageWorld

MakeGame
