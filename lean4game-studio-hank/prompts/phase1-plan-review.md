# Plan Review

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Context

You are reviewing the course plan (PLAN.md) for a lean4game course. This happens after the coverage mapper and course architect have produced their outputs, before any worlds are authored.

A bad plan means every world built on it is wasted work. This review catches structural problems before they compound.

Read `pipeline-state.json` to get `currentCourse`.
Read `current-course.txt` for the course directory name.
Read `{course}/PLAN.md` — the course plan to review.
Read `{course}/coverage-map.md` — the coverage map it was built from.
Read `long_term.md` for the course description and scope.

## What to evaluate

### 1. Scope completeness

Does the plan cover everything described in `long_term.md` for this course? A "well covered" course should cover its FULL scope, including advanced topics. Check:
- Are all major theorem families from the course description represented in the world graph?
- Are there worlds missing for topics explicitly mentioned in `long_term.md`?
- Is the plan a shallow survey when it should be deep?

### 2. Coverage map alignment

Does the plan actually address what the coverage map identified? Check:
- Every core uncovered item from the coverage map — is there a world that covers it?
- Every weakly covered item — is there a plan to strengthen it?
- Example coverage gaps — are example/case-study worlds planned for major definitions?
- Are counterexamples planned?

### 3. World graph coherence

- Does each world have a clear, single center of gravity?
- Is the dependency ordering sound? (No world depends on material taught later)
- Is the mix of world types deliberate? (lecture, pset, example, review — not all one type)
- Are pset worlds paired with their lecture worlds?
- Are example worlds placed AFTER the abstract theory they concretize?

### 4. Proof-move coverage

- Does the plan teach proof moves, not just list theorems?
- Is there a clear proof-move map?
- Are proof moves practiced in multiple contexts (not just introduced once)?
- Does each world's boss integrate multiple proof moves?

### 5. Granularity plan

- Is each world's level ladder sketched with dominant lessons?
- Are novelty budgets reasonable (at most 1 new burden per level)?
- Are bosses mapped to their seeded subskills?

### 6. Transfer plan

- Is there a real transfer plan (not just "psets exist")?
- For each high-value move: where introduced, where practiced, where retrieved, where transferred?
- Are there review/consolidation worlds where needed?

### 7. Inventory release plan

- Are tactics/theorems/definitions released at appropriate times?
- Is there a deliberate progression from restricted to full inventory?
- Are dangerous automation tactics (simp, decide, omega) gated?

### 8. Example and counterexample plan

- Does every major definition have at least one planned concrete example?
- Are counterexamples planned for important theorems?
- Are example worlds substantial (not just one-off levels)?

## Output

Write your output to `{course}/reviews/plan-review-current.md`.

Format as:

1. **Scope assessment**: Does the plan cover the full scope? What's missing?
2. **Coverage alignment**: Does it address the coverage map findings?
3. **World graph issues**: Structural problems in the world graph
4. **Proof-move gaps**: Proof moves that are listed but not actually taught
5. **Granularity issues**: Worlds that are too broad, too thin, or badly cut
6. **Transfer gaps**: High-value moves with no transfer plan
7. **Example gaps**: Major definitions with no concrete example
8. **P0 defects** (blocking): Fundamental plan problems that would waste all downstream work
9. **P1 defects** (high): Significant gaps that would degrade the course
10. **P2 defects** (medium): Improvements worth making
11. **Specific recommendations**: Ranked list of changes to PLAN.md
12. **Overall verdict**: PASS or FAIL

A plan FAILS if:
- Major topics from `long_term.md` are missing
- The proof-move map is absent or superficial
- More than 3 major definitions have no example plan
- The world graph has dependency errors
- The transfer plan is absent

## State update

After writing the review, update `pipeline-state.json`:
- Set `nextStep` to `"plan-gate"`
