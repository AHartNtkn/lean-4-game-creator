# Cross-World Coverage Remap

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Context

You are performing a cross-world coverage analysis after all worlds in a course have been authored and reviewed. This is Phase 3a.

Read `pipeline-state.json` to get `currentCourse`.
Read `current-course.txt` for the course directory name.
Read `{course}/PLAN.md` for the course architecture.
Read `{course}/coverage-map.md` for the original Phase 1 coverage map.

## What to read

Read ALL completed world files:
- `{course}/Game/Levels/**/*.lean` — all level files across all worlds
- `{course}/Game.lean` — game structure and dependencies

## Your task

Re-map coverage across all completed worlds. You are looking for issues that only become visible when you see the whole course at once:

### 1. Coverage drift

Items that the plan said would be covered but aren't. Check:
- Every MATH item from the coverage map — is it actually introduced and practiced?
- Every MOVE item — is the proof strategy actually taught, not just used?
- Every LEAN item — is the tactic actually taught with a level?
- Every EXAMPLE item — are major definitions concretized?

### 2. Coverage gaps

Items that fell through the cracks between worlds:
- Theorem families split across worlds where no single world provides closure
- Proof moves used in later worlds but never explicitly taught
- Notation introduced without explanation
- Misconceptions never addressed

### 3. Redundancy

- Content repeated across worlds with no new demand
- Levels in different worlds that teach the same move on the same surface form
- Excessive warm-up that could be consolidated

### 4. Transfer gaps

- High-value moves that are only practiced in one context
- Missing pset coverage for lecture content
- Bosses that don't connect to the broader course

### 5. Example gaps

- Major definitions never exercised on a concrete object
- Missing counterexamples for important theorems
- Concrete objects that should be revisited through a new theoretical lens but aren't

### 6. Granularity issues visible only at course scale

- Worlds that should be merged (each too thin alone)
- Worlds that should be split (discovered to have two centers of gravity during authoring)
- Level density imbalances (one world has 20 levels, an adjacent equally important world has 4)

## Output

Write two files:

### {course}/coverage-map-final.md

Updated coverage map reflecting the actual state of all worlds. Same 11-section format as the original.

### {course}/cross-world-issues.md

List of issues found, ranked by severity:
- **P0** (blocking): coverage gaps that leave core items untaught
- **P1** (high): significant redundancy or transfer gaps
- **P2** (medium): minor issues or opportunities
- **None**: if no issues found (unlikely but possible)

For each issue, specify:
- What the issue is
- Which worlds are affected
- Suggested fix

## State update

After writing both files, update `pipeline-state.json`:
- Set `nextStep` to `"cross-world-fix"`
