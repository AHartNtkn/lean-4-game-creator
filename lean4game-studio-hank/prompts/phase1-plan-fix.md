# Plan Fix

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Context

You are fixing issues found in the course plan review. This updates PLAN.md and potentially coverage-map.md.

Read `pipeline-state.json` to get `currentCourse`.
Read `current-course.txt` for the course directory name.
Read `{course}/reviews/plan-gate-decision.json` — the gate's decision with defects and recommendations.
Read `{course}/reviews/plan-review-current.md` — the full review.
Read `{course}/PLAN.md` — the current plan.
Read `{course}/coverage-map.md` — the coverage map.
Read `long_term.md` for the course scope.

## Quick exit

If the gate decision says `"done"`, write `NO_FIXES_NEEDED` to `codon-output.txt` and stop. Set `pipeline-state.json.nextStep` to `"author-world"`.

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

## State update

After fixing, update `pipeline-state.json`:
- Set `nextStep` to `"plan-review"` (loop back for re-review)
- Increment `reviewRound` by 1
