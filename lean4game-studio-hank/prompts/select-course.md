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

### Output

Print ONLY the **exact directory name** of the selected course. This MUST be a directory that exists in the project root and contains a `Game.lean` file. Run `ls` to verify the directory exists. Do NOT invent a name — use the actual directory name from the filesystem.

If ALL courses are complete, print `ALL_COURSES_COMPLETE`.

Do NOT create any files. Do NOT write to `current-course.txt` or `pipeline-state.json`. Just print the directory name.
