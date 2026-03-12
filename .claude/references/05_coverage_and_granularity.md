# Coverage and granularity

This file is the heart of the pack.

Good lean4game design requires explicit control of **coverage** and **granularity**.

## 1. Coverage is multidimensional

Track every important item on one of these axes:

- **MATH**: definitions, objects, theorem families
- **MOVE**: proof strategies and proof shapes
- **LEAN**: tactics, commands, proof-state manipulations
- **NOTATION**: syntax, coercions, binder forms, absolute values, function application, etc.
- **MISCONCEPTION**: predictable false moves or confusions
- **TRANSFER**: plain-language proof heuristics and recognizable patterns that should survive outside Lean

A course has bad coverage if it only tracks MATH.

## 2. Granularity exists at three levels

### Macro granularity: the course
The course should be chunked into world-sized chapters with a clear progression.

Example:
- onboarding
- limits of sequences
- algebraic limit theorems
- Cauchy machinery
- subsequences
- completion / reals
- series
- continuity / derivatives
- integration
- compactness / topology

### Meso granularity: the world
A world should cover one theorem family or one coherent cluster of proof moves.

Good centers of gravity:
- unpacking convergence definitions
- proving algebraic limit laws
- contradiction-based order theorems
- subsequence construction
- manipulating conjunctions / disjunctions
- induction and finite sums

### Micro granularity: the level
A level should usually isolate one dominant lesson:
- one new proof move,
- one new tactic,
- one subtle notation issue,
- one definition in action,
- one transfer opportunity,
- or one integration task.

## 3. Coverage states

Every important item should be labeled with one or more of these states:

- **I** = introduce
- **S** = supported practice
- **R** = unsupported retrieval
- **G** = integration into a bigger proof
- **T** = transfer to a fresh surface form
- **W** = warning / misconception handling

If an item never progresses beyond I, coverage is weak.

## 4. Coverage schema

For each item, maintain a row with these fields:

- item name
- axis (`MATH`, `MOVE`, `LEAN`, `NOTATION`, `MISCONCEPTION`, `TRANSFER`)
- importance (`core`, `supporting`, `optional`)
- first introduction
- supported practice locations
- retrieval locations
- integration locations
- transfer locations
- warnings / misconceptions
- notes on local style or special notation

Example rows:

- `SeqLim` — `MATH`
- unfold a definition with `change` — `MOVE` + `LEAN`
- choose epsilon witness / N witness — `MOVE`
- `|a n - L|` syntax with no interior spaces at the bars — `NOTATION`
- “strict inequalities do not transfer to the limit” — `MISCONCEPTION`
- “state the proof in plain English after the Lean proof” — `TRANSFER`

## 5. Granularity tests

### A level is too broad if:
- the solution requires multiple untaught micro-skills;
- the failure points span unrelated categories;
- the author cannot summarize the level’s main lesson in one sentence;
- or the post-level conclusion needs three different recipes.

### A level is too fine if:
- it differs from neighbors only by renaming;
- it teaches no reusable move;
- or the learner could have gained the same value from one stronger transfer problem.

### A world is too broad if:
- the boss needs ideas that belong to two separate theorem families,
- or the intro cannot explain the world’s purpose without becoming a chapter summary.

### A world is too fine if:
- it has no boss-worthy integration,
- or it could be absorbed into adjacent worlds without loss of clarity.

## 6. Novelty budget

Track novelty on four dimensions:

- new mathematics
- new proof move
- new Lean move
- new notation

Rule of thumb:
- early levels: at most one of these should be truly new
- mid-course: two can be new if the other two are stable
- bosses: should integrate prior novelty rather than introduce fresh novelty
- psets: mostly reuse prior novelty, with only occasional low-load additions

## 7. Coverage closure before a boss

Before a boss uses a move or concept heavily, the learner should usually have seen:

1. a clean introduction,
2. a low-load worked example,
3. one or two supported practice uses,
4. at least one retrieval opportunity,
5. and ideally one warning or contrast case.

A boss should reveal weakness, not ambush the learner.

## 8. What the real-analysis example suggests

The visible design logic appears to be:

- **coverage** follows the real course syllabus;
- **granularity** follows proof moves.

Lecture 1 covers basic tactics because those are the moves needed to read goals and use hypotheses.
Lecture 2 introduces `SeqLim` through a constant-sequence theorem because the theorem is mathematically easy and therefore isolates:
- unfolding a definition,
- introducing quantifiers,
- choosing a witness,
- rewriting with a hypothesis,
- and normalizing a trivial absolute value.

That is a canonical example of good granularity.

## 9. Required outputs from any planning step

Any good planner in this pack should be able to produce:

- a course coverage map,
- a world-by-world granularity plan,
- a novelty budget,
- a gap report,
- a redundancy report,
- and a list of items with weak closure.

If it cannot, it does not understand the course well enough yet.
