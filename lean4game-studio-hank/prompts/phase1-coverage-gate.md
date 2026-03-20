# Coverage Gate

## Files to read FIRST

1. `current-course.txt` — the course directory name
2. `{course}/reviews/coverage-review-current.md` — the coverage review

You MUST read the ENTIRE review file.

## This is a READ-ONLY gate

You do NOT modify the coverage map. You read the review and write a decision.

## Pass criteria

The coverage map PASSES only if:
- No P0 defects (no core topics from `long_term.md` missing)
- No major mathlib discrepancies
- Proof-move clusters exist and are substantive
- Major definitions have example plans

## Decision logic

- If P0 defects exist → `"continue"` (must fix)
- If major mathlib discrepancies → `"continue"` (must fix)
- Otherwise → `"done"`

## Output

Write your output to `{course}/reviews/coverage-gate-decision.json`.

```json
{
  "action": "continue" | "done",
  "p0Defects": ["list"],
  "discrepancies": ["list"],
  "recommendations": ["list"],
  "notes": "free-form"
}
```
