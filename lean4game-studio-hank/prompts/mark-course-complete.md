# Mark Course Complete

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Context

You are marking a course as complete, committing it, and advancing to the next course. This is Phase 4.

Read `pipeline-state.json` to get `currentCourse`.
Read `current-course.txt` for the course directory name.
Read `catalog-progress.json` for the list of completed courses.

## Task

### 1. Verify the course is ready

Check that:
- `{course}/PLAN.md` exists
- `{course}/coverage-map-final.md` exists (cross-world review was done)
- `world-progress.json` has no stuck worlds
- The project builds cleanly (run `lake build` to verify)

If any check fails, write an error report and set `pipeline-state.json.nextStep` to `"done"`.

### 2. Commit the course

Run:
```bash
git add -A
git commit -m "Complete {course} course

Authored all worlds, passed enrichment review and playtest audit for each world,
passed cross-world coverage review.

Co-Authored-By: Claude <noreply@anthropic.com>"
git push
```

Replace `{course}` with the actual course name from `current-course.txt`.

### 3. Update catalog-progress.json

Add the course name to the `completed` array.

### 4. Clean up working files

- Remove `current-world.txt`
- Remove `world-progress.json`
- Remove `build-log.txt`, `build-exit-code.txt` if they exist
- Remove `should-run.txt`, `codon-output.txt` if they exist
- Keep `pipeline-state.json` and `catalog-progress.json`

### 5. Advance to next course

Update `pipeline-state.json`:
- Set `nextStep` to `"select-course"`
- Set `currentCourse` to `null`
- Set `currentWorld` to `null`
- Clear `worldsCompleted` to `[]`
- Set `reviewRound` to `0`
- Set `reviewCycleCount` to `0`

## Important

- This codon commits ALL changes in the working directory. Make sure nothing unwanted is staged.
- The commit message should accurately describe what was accomplished.
- If the push fails (e.g., network issue), do NOT retry automatically. Write an error report.
