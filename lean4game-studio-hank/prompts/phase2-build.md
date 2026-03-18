# Build and Fix

## Context

You are building the lean4game project and fixing any compilation errors. This is Phase 2b.

The rig has already run `lake build` and captured the output to `build-log.txt` with the exit code in `build-exit-code.txt`.

Read `current-course.txt` and `current-world.txt` for context.

## Task

### If the build succeeded (exit code 0)

The build is clean. No action needed.

### If the build failed (exit code non-zero)

Read `build-log.txt` carefully. Identify ALL compilation errors.

Fix the errors in the source `.lean` files. Common issues:
- Missing imports
- Type mismatches
- Incorrect tactic names
- Missing theorem/definition references
- Syntax errors in hints (especially `{curly braces}` which are interpolation)
- `NewHiddenTheorem` (doesn't exist — use `NewHiddenTactic`)
- `show`/`change` not escaped as `«show»`/`«change»` in TacticDoc

After fixing, rebuild:
```
lake build 2>&1 | tee build-log.txt
echo $? > build-exit-code.txt
```

You may attempt up to 3 fix-rebuild cycles. If the build still fails after 3 attempts, write an error report to `build-failure-report.txt` explaining what went wrong.

## Important

- Do NOT change the mathematical content or pedagogical structure of levels to fix build errors.
- Only fix actual compilation issues.
- If a build error reveals a fundamental design problem (e.g., a required mathlib definition doesn't exist), document it but don't try to work around it with incorrect math.
