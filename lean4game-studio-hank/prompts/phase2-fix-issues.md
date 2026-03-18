# Fix Issues

## Context

You are fixing issues found by the enrichment reviewer and playtest auditor. This is Phase 2f.

Read `current-course.txt` and `current-world.txt` for context.

## Inputs to read

1. `{course}/reviews/gate-decision.json` — the gate's decision, including lists of defects and suggestions
2. `{course}/reviews/enrichment-current.md` — the full enrichment review
3. `{course}/reviews/playtest-current.md` — the full playtest audit
4. All level files for the current world: `{course}/Game/Levels/{world}/*.lean`
5. World base file: `{course}/Game/Levels/{world}.lean`
6. `{course}/Game.lean` — game structure

## Quick exit

Read `gate-decision.json`. If the `action` field is `"done"`, write `NO_FIXES_NEEDED` to `codon-output.txt` and stop immediately.

## Fix rules — THESE ARE NON-NEGOTIABLE

### P0 defects: MUST fix all

Every P0 defect listed in gate-decision.json MUST be fixed. No exceptions. No "not blocking." No "close enough."

### P1 defects: MUST fix all

Every P1 defect MUST be fixed. These are high priority, not optional.

### Enrichment suggestions: implement ALL that are marked "yes" (recommended)

The enrichment reviewer's suggestions carry weight. You must NEVER reject an enrichment suggestion because:
- It would make the world "too big"
- The change would be "too large" (splitting a world, adding multiple levels)
- You want to minimize effort or avoid rework
- The world "already works" or "compiles fine"

The ONLY valid reason to reject is that implementing it would make the world pedagogically WORSE.

### P2 defects: fix if possible

Fix P2s unless doing so would conflict with higher-priority fixes.

## What to fix

Common fixes:
- **Exploitable statements**: Add `DisabledTheorem` or `DisabledTactic` for specific levels. When disabling for Finset operations, ALSO check lattice-level aliases (sup_comm, inf_le_left, le_antisymm, sup_le, sup_eq_left, etc.).
- **Missing hints**: Add layered hints at the actual stuck states learners will reach
- **Missing docs**: Add TacticDoc/TheoremDoc/DefinitionDoc entries
- **Overbroad levels**: Split into multiple levels with one dominant lesson each
- **Missing examples**: Add concrete computation or counterexample levels
- **Boss issues**: Ensure boss integrates 3+ moves, all seeded in prior levels
- **Missing coverage closure**: Add practice/retrieval levels for under-covered moves
- **Interactive proof issues**: Replace elaborate one-liners with `apply` + focused subgoals

## Operational rules

- DisabledTactic baseline: `trivial decide native_decide simp aesop simp_all`
- `norm_num` and `linarith` — disable per-level when teaching manual reasoning
- `tauto` — disable when teaching logic
- Hint strings: NO `{curly braces}` (GameServer interpolation)
- `show`/`change` are keywords: `«show»`/`«change»` for TacticDoc
- `NewHiddenTheorem` does not exist — only `NewHiddenTactic`
- One `NewTheorem`/`NewTactic`/`NewDefinition` per type per level — combine multiples
- `TacticDoc` must appear before `DisabledTactic` in same file

## After fixing

Rebuild the project:
```
lake build 2>&1 | tee build-log.txt
echo $? > build-exit-code.txt
```

If the build fails, fix the errors and rebuild. Up to 3 attempts.

