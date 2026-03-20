# Plan Fix

## Context

You are fixing issues found in the course plan review. This updates PLAN.md.

## Files to read FIRST

1. `current-course.txt` — the course directory name
2. `{course}/reviews/plan-gate-decision.json` — the gate's decision with defects and recommendations
3. `{course}/PLAN.md` — the current plan
4. `{course}/coverage-map.md` — the coverage map (read-only reference)
5. `long_term.md` — the course scope

## Fix rules

### P0 defects: MUST fix all

Missing topics, absent proof-move maps, dependency errors — these are structural. Fix them in PLAN.md.

### P1 defects: MUST fix all

Significant gaps in examples, transfer, granularity — fix them.

### Recommendations: implement all that improve the plan

Do NOT reject recommendations because they make the plan bigger. A plan that needs 20 worlds should have 20 worlds. A plan that needs example worlds for every major definition should have them.

## What you MUST change

- `{course}/PLAN.md` — all fixes go here. Add worlds, restructure the graph, add proof-move coverage, add examples, fix dependencies, improve transfer plan.

## What you MUST NOT change

- `{course}/coverage-map.md` — the coverage map is finalized before planning. Do not modify it.
- Level files (none exist yet)
- Game.lean (not yet)

## Clean up review files

After all fixes are applied, delete the review files so the next review round starts fresh:

```
rm {course}/reviews/plan-review-current.md
rm {course}/reviews/plan-gate-decision.json
```

This is mandatory. The next round's reviewer must evaluate the plan on its own merits.

