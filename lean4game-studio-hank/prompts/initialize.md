# Initialize Pipeline State

You are initializing the lean4game course production pipeline.

## Task

Check if `pipeline-state.json` and `catalog-progress.json` exist in the current directory. If they already exist and contain valid JSON, leave them as-is. If they don't exist or are empty/invalid, create them with these defaults:

### pipeline-state.json
```json
{
  "nextStep": "select-course",
  "currentCourse": null,
  "currentWorld": null,
  "reviewRound": 0,
  "coursesCompleted": [],
  "worldsCompleted": [],
  "reviewCycleCount": 0
}
```

### catalog-progress.json
```json
{
  "completed": []
}
```

If the files already exist with valid content, report what state the pipeline is in (which course, which step) and do nothing else.

Write "Initialization complete." when done.
