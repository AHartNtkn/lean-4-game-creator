# Plan Gate

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Context

You are the quality gate for a course plan. You read the plan review and decide whether the plan is ready for world authoring.

Read `pipeline-state.json` to get `currentCourse` and `reviewCycleCount`.
Read `current-course.txt` for the course directory name.
Read `{course}/reviews/plan-review-current.md` — the plan review.

You MUST read the ENTIRE review file. Do not skim.

## This is a READ-ONLY gate

You do NOT modify the plan. You do NOT write code. You read the review and write a decision.

## Pass criteria

A plan PASSES only if ALL of:
- No P0 defects
- No P1 defects
- The scope covers the full course description from long_term.md
- The proof-move map exists and is substantive
- Major definitions have example plans
- The transfer plan exists

## First review never passes

If `reviewCycleCount` is 0 (first review of this plan), set action to `"continue"` regardless. First reviews always find issues.

## Review round limits

If `reviewCycleCount` reaches 5 and P0 defects remain, set action to `"abort"`.

## Output

Write your output to `{course}/reviews/plan-gate-decision.json`.

```json
{
  "action": "continue" | "done" | "abort",
  "reviewRound": <current round>,
  "p0Defects": ["list"],
  "p1Defects": ["list"],
  "p2Defects": ["list"],
  "recommendations": ["ranked list of changes to implement"],
  "notes": "free-form"
}
```

## State update

After writing the decision:
- If action is `"done"`: set `nextStep` to `"author-world"`
- If action is `"continue"`: set `nextStep` to `"plan-fix"`, increment `reviewCycleCount` by 1
- If action is `"abort"`: set `nextStep` to `"done"` (halt pipeline)
