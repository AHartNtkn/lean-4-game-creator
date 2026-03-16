# Mark World Complete

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Context

You are marking a world as complete and archiving its review files. This is Phase 2g.

Read `pipeline-state.json` to get `currentCourse`, `currentWorld`, `reviewCycleCount`.
Read `current-course.txt` and `current-world.txt` for context.
Read `{course}/reviews/gate-decision.json` for the final gate decision.
Read `world-progress.json` for the current progress.

## Task

### If gate-decision says "done" (world passed)

1. Update `world-progress.json`:
   - Add the current world name to the `completed` array
   - Set `current` to `null`

2. Archive review files:
   - Rename `{course}/reviews/enrichment-current.md` → `{course}/reviews/enrichment-{world}-final.md`
   - Rename `{course}/reviews/playtest-current.md` → `{course}/reviews/playtest-{world}-final.md`
   - Rename `{course}/reviews/gate-decision.json` → `{course}/reviews/gate-{world}-final.json`

3. Update `pipeline-state.json`:
   - Set `nextStep` to `"author-world"` (to attempt the next world)
   - Set `currentWorld` to `null`
   - Set `reviewRound` to `0`
   - Set `reviewCycleCount` to `0`
   - Add the world name to `worldsCompleted` array

### If gate-decision says "abort" (world stuck)

1. Update `world-progress.json`:
   - Set `current` to `null`
   - Add a `"stuck"` field with the world name

2. Archive review files with `-stuck` suffix.

3. Update `pipeline-state.json`:
   - Set `nextStep` to `"done"` (halt the pipeline)

4. Write a report to `stuck-world-report.txt` explaining:
   - Which world is stuck
   - How many review cycles were attempted
   - What P0 defects remain
   - That human intervention is required

### If gate-decision is missing or invalid

Something went wrong. Write an error to `codon-output.txt` and set `pipeline-state.json.nextStep` to `"done"`.

## Important

- A stuck world means the ENTIRE pipeline halts. This is by design. The "FAIL means STOP" rule is structural.
- Do NOT move on to the next world if the current one is stuck.
- Do NOT set nextStep to "author-world" if the gate said "abort".
