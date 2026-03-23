import GameServer.Commands

import Game.Levels.SetWorld
import Game.Levels.SubsetWorld
import Game.Levels.SetOpsWorld

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
Dependency SetWorld → SubsetWorld
Dependency SetWorld → SetOpsWorld
Dependency SubsetWorld → SetOpsWorld

MakeGame
