# Cross-World Fix

## Context

You are fixing cross-world issues found during the coverage remap. This is Phase 3b.

## Files to read FIRST

1. `current-course.txt` — the course directory name
2. `{course}/cross-world-issues.md` — the list of issues from the coverage remap
3. `{course}/PLAN.md` — the course architecture
4. `{course}/Game.lean` — game structure

## Task

### If no issues found

If `cross-world-issues.md` says "None" or has no P0/P1/P2 issues, write `NO_FIXES_NEEDED` to `codon-output.txt`.

### If issues exist

Read all issues. Fix them in priority order (P0 first, then P1, then P2).

Common fixes:
- **Coverage gaps**: Add levels to existing worlds or create a new bridge world
- **Transfer gaps**: Add pset levels or transfer exercises
- **Example gaps**: Add computation levels or counterexample levels
- **Redundancy**: Remove duplicate levels, consolidate worlds
- **Granularity issues**: Split or merge worlds, adjust level density

When adding new content:
- Follow the same authoring rules as the world-author codon
- Check for exploit vectors (lattice aliases, fin_cases, etc.)
- Ensure proofs are interactive (no elaborate one-liners)
- Write complete code, no stubs

When modifying existing content:
- Preserve the world's center of gravity
- Update Game.lean if imports/dependencies change
- Update inventory commands if needed

### After fixing

Rebuild the project:
```
lake build 2>&1 | tee build-log.txt
echo $? > build-exit-code.txt
```

If the build fails, fix errors and rebuild (up to 3 attempts).

## Operational rules

- DisabledTactic baseline: `trivial decide native_decide simp aesop simp_all`
- Hint strings: NO `{curly braces}`
- `show`/`change` keywords: use `«show»`/`«change»` for TacticDoc
- One `NewTheorem`/`NewTactic`/`NewDefinition` per type per level
- `TacticDoc` before `DisabledTactic` in same file

