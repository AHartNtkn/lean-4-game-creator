# Failure taxonomy

Use this file to diagnose why a technically correct draft is still bad.

## 1. Hidden prerequisite leak
The level assumes a move or fact that was never isolated earlier.

Repair:
- add a precursor level,
- add a bridging hint,
- or weaken the level so it only uses taught moves.

## 2. Overbroad level
A learner can fail for many unrelated reasons:
- notation,
- theorem search,
- proof shape,
- algebra,
- and a new tactic all at once.

Repair:
- split the level,
- or remove one burden by pre-teaching it.

## 3. Overfine level
Several adjacent levels differ only by superficial renaming or arithmetic constants.

Repair:
- merge them,
- or replace duplicates with a transfer problem.

## 4. Surface coverage only
A theorem is stated and proved once, but never revisited under new conditions.

Repair:
- add supported reuse,
- unsupported retrieval,
- and transfer.

## 5. Inventory swamp
The player sees too many items, too early, with poor docs.

Repair:
- delay unlocks,
- hide aliases,
- use tabs,
- and improve doc entries.

## 6. Spoiler hint
The hint gives the exact move before the learner has had a real chance to think.

Repair:
- replace with a state-reading hint or strategy hint,
- move the direct answer to a hidden rescue layer.

## 7. Misfiring hint
Because hints are context-aware, not history-aware, the hint does not appear when the real stuck state occurs.

Repair:
- relocate the hint,
- use `Branch`,
- or add strict matching where needed.

## 8. Fake boss
The boss is just a longer instance of one earlier move.

Repair:
- redesign the boss to require at least three distinct moves from the world’s repertoire.

## 9. Lottery boss
The boss requires a trick that was never isolated or motivated.

Repair:
- seed the trick earlier,
- or change the boss.

## 10. Narrative drift
The intro talks about one thing; the actual levels teach another.

Repair:
- rewrite the intro,
- or realign the levels.

## 11. No consolidation
The conclusion says only “well done.”

Repair:
- summarize the method,
- translate to natural language,
- or point to the next reuse context.

## 12. Syntax dominates math
The learner spends more effort on surface Lean than on proof structure.

Repair:
- simplify the statement,
- add docs,
- add a template only if justified,
- or pre-teach the syntax on easier math.

## 13. Expert hostility
The course rejects obvious aliases or conventions known to more experienced Lean users.

Repair:
- support common aliases via hidden tactics where safe,
- but keep the visible inventory clean.

## 14. Missing discoverability
A theorem or tactic exists but its docs do not tell the learner when or how to use it.

Repair:
- add exact syntax,
- a minimal example,
- and a warning.

## 15. Dependency drift
World dependencies no longer match conceptual prerequisites after expansion.

Repair:
- re-run dependency reasoning manually,
- then patch `Game.lean`.

## 16. Update-only thinking
A technical update ships without replaying the learner path.

Repair:
- playtest critical worlds after every update,
- especially onboarding and latest additions.
