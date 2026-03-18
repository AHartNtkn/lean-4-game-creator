# Select Next Course

## Task

Select the next course to build from the lean4game catalog.

### Inputs to read

1. `long_term.md` — the course catalog with descriptions, prerequisites, and tags
2. `catalog-progress.json` — tracks which courses are already complete
3. `pipeline-state.json` — current pipeline state
4. List the directories in the project root to see what courses exist

### Selection rules

Select the next course that satisfies ALL of:

1. **Not yet complete**: not listed in `catalog-progress.json.completed`
2. **Prerequisites satisfied**: all prerequisite courses are in the completed list
3. **Prefer "well covered"** over "needs extension"
4. **Prefer "basic"** over advanced

### CRITICAL: Use the exact directory name

Run `ls` on the project root to see the actual course directories. Each course has a directory containing `Game.lean`. The directory name IS the course name. Do NOT invent names. Do NOT rename directories. Do NOT add prefixes like "lean4game-". Use the exact directory name as it appears on disk.

For example, if `ls` shows `functions_relations/Game.lean`, the course name is `functions_relations`, not `lean4game-functions-relations` or anything else.

### Output

1. Write the selected course's **exact directory name** (as shown by `ls`) to `current-course.txt`
2. If ALL courses are complete, write `ALL_COURSES_COMPLETE` to `current-course.txt`
3. Update `pipeline-state.json`: set `currentCourse` to the exact same directory name, clear `currentWorld` to null, clear `worldsCompleted` to `[]`, reset `reviewRound` and `reviewCycleCount` to 0.
