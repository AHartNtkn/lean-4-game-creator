# Coverage Mapper

## Context

You are building a coverage map for a lean4game course. This is Phase 1a of the course production pipeline.

## Files to read FIRST

1. `current-course.txt` — the course directory name
2. `long_term.md` — course description, scope, prerequisites, and coverage tags
3. `{course}/Game.lean` — current game structure
4. `{course}/Game/Levels/**/*.lean` — any existing level files

## Your role

This skill exists because a course can have excellent individual levels and still be bad overall. You are building the map that prevents this.

## Core principle

Each course must be **full**, including advanced topics. Do not produce a shallow survey — cover the subject thoroughly, with depth proportional to what mathlib supports. Use the course description in `long_term.md` as the scope definition, and map everything within that scope.

Map **what** the course covers and **how finely** it covers it.

Coverage without granularity yields broad, frustrating levels.
Granularity without coverage yields elegant fragments and an incomplete course.

## Build the coverage map

Track items on at least these axes:

- `MATH` — definitions, objects, theorem families
- `MOVE` — proof strategies and proof shapes
- `LEAN` — tactics, commands, proof-state manipulations
- `NOTATION` — syntax, coercions, binder forms
- `MISCONCEPTION` — predictable false moves or confusions
- `TRANSFER` — plain-language proof heuristics that survive outside Lean
- `EXAMPLE` — concrete mathematical objects that instantiate the theory

For each important item, record:
- importance (core / supporting / optional)
- what levels/worlds should introduce it
- what levels/worlds should provide supported practice
- what levels/worlds should require unsupported retrieval
- what levels/worlds should integrate it into larger proofs
- what levels/worlds should transfer it to a fresh surface form
- warning/misconception handling needs

If any of these cells would be blank for a core item, say so plainly. Gaps are information.

## Build the granularity map

At three scales:

### Course scale
What are the macro modules or world clusters?

### World scale
What is each world's single center of gravity?

### Level scale
What is each level's dominant lesson?

If you cannot state a level's dominant lesson in one sentence, the level is probably badly cut.

## Enforce novelty budgets

For every level or world, track whether it introduces:
- new mathematics
- new proof move
- new Lean move
- new notation

Flag any place where novelty is too concentrated.

## Analyze closure

For each core concept or move, decide whether closure is:
- **strong**: intro + support + retrieval + integration + transfer
- **partial**: some stages present, some absent
- **weak**: barely introduced
- **illusory**: appears covered only because it is mentioned, not because the learner practices it

## Analyze example coverage

For each major definition in the course, check whether it has been exercised on at least one concrete example. Flag definitions that are only used abstractly.

Specifically check:
- Has the learner computed or verified this property for a specific object?
- Has the learner seen a counterexample — an object that fails to satisfy the definition?
- Are example worlds placed so they concretize theory the learner has already seen?
- Do the examples chosen cover enough variety?

## Analyze redundancy

Find content that is:
- repeated with no new demand
- repeated only at the surface level
- or repeated so often that it consumes space needed for missing coverage

## Analyze granularity defects

Explicitly flag:
- overbroad levels
- overfine levels
- worlds that should be split
- worlds that should be merged
- bosses that lack closure
- theorem families whose micro-moves were never isolated

## Granularity must come from proof moves, not from the syllabus

When the mathematical syllabus is already known, do not use the syllabus itself as the granularity plan. Textbook sections and theorem lists are too coarse. Instead:
1. Keep the syllabus as macro coverage
2. Derive theorem families from the syllabus
3. Derive proof-move clusters from those families
4. Cut levels around those clusters

## Reading the current course state

Since all courses start as stubs (Welcome level only), you are mapping what the course SHOULD cover, not what it currently contains. Use the course description from `long_term.md` and your knowledge of the mathematical content to build the map.

Read the course's existing files:
- `{course}/Game.lean` — current game structure
- `{course}/Game/Levels/**/*.lean` — existing level files (likely just Welcome)

## Output

Write your output to `{course}/coverage-map.md` where `{course}` is the value from `current-course.txt`.

The output must contain these 11 sections:

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

