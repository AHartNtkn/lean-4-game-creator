---
name: lean4game-coverage-mapper
description: Use this whenever the task involves planning or auditing a lean4game course, world, or level sequence. This skill builds the coverage map and checks granularity. It is mandatory before serious planning because theorem lists alone do not tell you whether the course actually teaches the necessary proof moves, Lean moves, notation, and misconceptions.
---

# lean4game-coverage-mapper

This skill exists because a course can have excellent individual levels and still be bad overall.

Read:
- `references/05_coverage_and_granularity.md`
- `references/03_quality_rubric.md`
- `references/04_failure_taxonomy.md`

## Core principle

Map **what** the course covers and **how finely** it covers it.

Coverage without granularity yields broad, frustrating levels.  
Granularity without coverage yields elegant fragments and an incomplete course.

## Build the coverage map

Track items on at least these axes:

- `MATH`
- `MOVE`
- `LEAN`
- `NOTATION`
- `MISCONCEPTION`
- `TRANSFER`
- `EXAMPLE`

For each important item, record:
- importance,
- first introduction,
- supported practice,
- unsupported retrieval,
- integration,
- transfer,
- and warning/misconception handling.

If any of these cells are blank for a core item, say so plainly.

## Build the granularity map

At three scales:

### Course scale
What are the macro modules or world clusters?

### World scale
What is each world’s single center of gravity?

### Level scale
What is each level’s dominant lesson?

If you cannot state a level’s dominant lesson in one sentence, the level is probably badly cut.

## Enforce novelty budgets

For every level or world, track whether it introduces:
- new mathematics,
- new proof move,
- new Lean move,
- new notation.

Flag any place where novelty is too concentrated.

## Analyze closure

For each core concept or move, decide whether closure is:

- **strong**: intro + support + retrieval + integration + transfer
- **partial**: some stages present, some absent
- **weak**: barely introduced
- **illusory**: appears covered only because it is mentioned, not because the learner practices it

## Analyze example coverage

For each major definition in the course, check whether it has been exercised
on at least one concrete example. Flag definitions that are only used
abstractly — the learner may be able to manipulate quantifiers without
understanding what the definition looks like in practice.

Specifically check:
- Has the learner computed or verified this property for a specific object?
- Has the learner seen a counterexample — an object that fails to satisfy
  the definition — so they understand why the conditions matter?
- Are example worlds placed so they concretize theory the learner has already
  seen, rather than appearing before the abstract definitions?
- Do the examples chosen cover enough variety (abelian vs non-abelian, finite
  vs infinite, familiar vs exotic)?

## Analyze redundancy

Find content that is:

- repeated with no new demand,
- repeated only at the surface level,
- or repeated so often that it consumes space needed for missing coverage.

## Analyze granularity defects

Explicitly flag:

- overbroad levels
- overfine levels
- worlds that should be split
- worlds that should be merged
- bosses that lack closure
- theorem families whose micro-moves were never isolated

## Output format

Return:

1. **Coverage matrix summary**
2. **Core uncovered items**
3. **Weakly covered items**
4. **Example coverage gaps** — definitions exercised only abstractly, missing counterexamples
5. **Redundant items**
6. **Granularity defects**
7. **Novelty hotspots**
8. **Recommended splits/merges**
9. **Recommended new levels or new worlds** (including example/case-study worlds)
10. **Items that should be demoted, delayed, or hidden in the inventory**
11. **Confidence notes**

## Granularity must come from proof moves, not from the syllabus

When the mathematical syllabus is already known, do not use the
syllabus itself as the granularity plan. Textbook sections and theorem
lists are too coarse — they tell you what to prove, not what the
learner needs to practice.

Instead:
1. keep the syllabus as macro coverage,
2. derive theorem families from the syllabus,
3. derive proof-move clusters from those families,
4. and cut levels around those clusters.

This applies to any course where the mathematical content is
predetermined — group theory, topology, linear algebra, or anything
else. The syllabus determines *what* to cover; the proof-move analysis
determines *how finely* to cut it.
