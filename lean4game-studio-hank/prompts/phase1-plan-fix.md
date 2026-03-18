# Plan Fix

## Context

You are fixing issues found in the course plan review. This updates PLAN.md and potentially coverage-map.md.

Read `current-course.txt` for the course directory name.
Read `{course}/reviews/plan-gate-decision.json` — the gate's decision with defects and recommendations.
Read `{course}/reviews/plan-review-current.md` — the full review.
Read `{course}/PLAN.md` — the current plan.
Read `{course}/coverage-map.md` — the coverage map.
Read `long_term.md` for the course scope.

## Quick exit

If the gate decision says `"done"`, write `NO_FIXES_NEEDED` to `codon-output.txt` and stop.

## Fix rules

### P0 defects: MUST fix all

Missing topics, absent proof-move maps, dependency errors — these are structural. Fix them in PLAN.md.

### P1 defects: MUST fix all

Significant gaps in examples, transfer, granularity — fix them.

### Recommendations: implement all that improve the plan

Do NOT reject recommendations because they make the plan bigger. A plan that needs 20 worlds should have 20 worlds. A plan that needs example worlds for every major definition should have them.

## What you may change

- `{course}/PLAN.md` — add worlds, restructure the graph, add proof-move coverage, add examples, fix dependencies, improve transfer plan
- `{course}/coverage-map.md` — update if the plan changes reveal coverage map errors

## What you may NOT change

- Level files (none exist yet)
- Game.lean (not yet)

## Clean up review files

After all fixes are applied, delete the review files so the next review round starts fresh:

```
rm {course}/reviews/plan-review-current.md
rm {course}/reviews/plan-gate-decision.json
```

This is mandatory. The next round's reviewer must evaluate the plan on its own merits.

