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

## Granularity guidance for the course architect

Granularity must come from proof moves, not from the syllabus. Textbook sections and theorem lists are too coarse. Instead:
1. Keep the syllabus as macro coverage
2. Derive theorem families from the syllabus
3. Derive proof-move clusters from those families
4. Identify which clusters deserve their own levels

Include this analysis in the coverage map so the course architect can cut levels properly.

## This is a PLANNING document, not a review

You are mapping what the course SHOULD cover. No worlds or levels exist yet. Do not write post-hoc review sections (granularity defects, splits/merges of existing content). Those belong in Phase 3 after content exists.

## Output

Write your output to `{course}/coverage-map.md` where `{course}` is the value from `current-course.txt`.

The output must contain these sections:

1. **Coverage matrix summary** — items across all 7 axes with importance and planned coverage stages
2. **Core items that must not be missed** — the most important things the course must teach
3. **Example plan** — which definitions need concrete examples, which need counterexamples, what objects to use
4. **Proof-move clusters** — groups of related proof moves that should be taught together
5. **Novelty hotspots** — places where too much novelty would concentrate if not carefully sequenced
6. **Items to demote, delay, or hide** — what should be gated, deferred, or kept out of inventory
7. **Confidence notes** — what you're sure about and what needs the architect's judgment

