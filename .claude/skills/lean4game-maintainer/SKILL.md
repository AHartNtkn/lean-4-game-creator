---
name: lean4game-maintainer
description: Use this when the user wants to expand, refactor, update, publish, or generally maintain a lean4game repo. This skill preserves house style, coverage, granularity, and learner experience while handling toolchain changes, issue-driven repairs, dependency drift, and release management.
---

# lean4game-maintainer

Maintenance is pedagogy with version control.

Read:
- `references/02_technical_levers.md`
- `references/03_quality_rubric.md`
- `references/04_failure_taxonomy.md`
- `references/05_coverage_and_granularity.md`

If the repo's style is unknown (written by someone else, or inherited from a previous session with no design artifacts), begin with:
1. `lean4game-pattern-miner`
2. `lean4game-coverage-mapper`

If you established the style yourself (via course-architect or by authoring the existing worlds), skip the pattern miner and begin with:
1. `lean4game-coverage-mapper`

## Maintenance modes

### 1. Technical update
Examples:
- Lean version bump
- mathlib drift
- local dev setup drift
- publish / import pipeline refresh

Tasks:
- update `lean-toolchain`
- update dependencies
- rebuild
- repair config drift
- replay critical learner paths
- confirm local run and publish path still work

### 2. Pedagogical repair
Examples:
- missing docs
- missing aliases
- brittle hints
- overbroad world
- hidden prerequisite leak
- pset clone problem

Tasks:
- identify the learner pain
- patch the level or world
- preserve house style
- update docs and hidden aliases where needed
- re-run playtest

### 3. Expansion
Examples:
- add a lecture world
- add a pset world
- extend a theorem family
- insert a bridge world

Tasks:
- compute the coverage diff
- choose insertion point
- patch dependencies
- preserve world rhythm
- update inventory expectations
- playtest the new seam, not just the new files

## Treat issues as evidence

When you see a user complaint, ask what it reveals.

Examples of meaningful signals:
- “I do not know how to use this tactic” -> docs or first-contact coverage is weak
- “The alias I expected is missing” -> expert-friction / discoverability problem
- “This level felt impossible” -> hidden prerequisite or granularity problem
- “I can solve examples but not the pset” -> transfer closure is weak

Do not dismiss these as mere UX polish.

## Required maintenance checks

Always check:

- house style drift
- dependency drift
- coverage drift
- world-size drift
- doc drift
- alias drift
- boss integrity drift
- local-run and publish path

## Technical workflow reminders

You should know the concrete maintenance path well enough to execute it without cargo-culting it.

Typical update path:
- edit `lean-toolchain`,
- run `lake update -R` and `lake build`,
- if local dev setup drift is the problem, refresh the setup files from `GameSkeleton`,
- replay learner-critical worlds locally,
- then republish and re-import.

Typical publish path:
- confirm the public repo and CI state are healthy,
- trigger import to the official server,
- then replay the published learner path, not merely the local one.

But never perform technical updates in a purely mechanical way. Recheck learner-critical worlds after every technical change.

## Output format

Return:

1. **Maintenance mode**
2. **Observed problems**
3. **Coverage / granularity impact**
4. **Files to edit**
5. **Patch plan**
6. **House-style constraints**
7. **Regression risks**
8. **Release notes phrased in learner-facing terms**
9. **Post-patch playtest plan**

If writing code, write full patches, not sketches.
