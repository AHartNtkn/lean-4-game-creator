# Select Next Course

## Task

Select the next course to build from the lean4game catalog.

### Inputs to read

1. `long_term.md` — the course catalog with descriptions, prerequisites, and tags
2. `catalog-progress.json` — tracks which courses are already complete
3. List the directories in the project root to see what courses exist

### Selection rules

Select the next course that satisfies ALL of:

1. **Not yet complete**: not listed in `catalog-progress.json.completed`
2. **Prerequisites satisfied**: all prerequisite courses are in the completed list
3. **Prefer "well covered"** over "needs extension"
4. **Prefer "basic"** over advanced

### Output

Write the selected course's **exact directory name** to `current-course.txt`. This MUST be a directory that exists in the project root and contains a `Game.lean` file. Run `ls` to verify the directory exists before writing. Do NOT invent a name — use the actual directory name from the filesystem.

If ALL courses are complete, write `ALL_COURSES_COMPLETE` to `current-course.txt`.
