# Coverage Fix

## Files to read FIRST

1. `current-course.txt` — the course directory name
2. `{course}/reviews/coverage-gate-decision.json` — the gate's decision
3. `{course}/reviews/coverage-review-current.md` — the full review
4. `{course}/coverage-map.md` — the current coverage map
5. `long_term.md` — the course scope

## Quick exit

If the gate decision says `"done"`, stop immediately. Do nothing.

## Fix rules

### P0 defects: MUST fix all

Missing core topics from `long_term.md` must be added to the coverage map with full axis coverage (MATH, MOVE, LEAN, NOTATION, MISCONCEPTION, TRANSFER, EXAMPLE).

### Mathlib discrepancies: MUST fix all

Use WebSearch and WebFetch to verify correct API names against current mathlib documentation. Update the coverage map with correct names.

### All other recommendations: implement if they improve completeness

## What you MUST change

- `{course}/coverage-map.md` — add missing items, fix API names, add example plans, add proof-move clusters

## Clean up review files

After all fixes are applied, delete the review files:

```
rm {course}/reviews/coverage-review-current.md
rm {course}/reviews/coverage-gate-decision.json
```
