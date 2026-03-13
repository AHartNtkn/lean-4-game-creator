# lean4game technical levers, interpreted pedagogically

This file is not a raw API summary. It explains what the main lean4game mechanisms are *for* in course design.

## 1. `Game.lean` is the course graph

Use `Game.lean` to define:
- imports for all worlds,
- title and high-level introduction,
- info / credits,
- and explicit `Dependency` edges where the automatically inferred graph is not pedagogically sufficient.

Interpretation:
- the dependency graph is your public statement of prerequisite structure;
- if the auto graph misses a conceptual prerequisite, add the edge yourself;
- if your world graph looks messy, your course design may be messy.

## 2. Inventory commands are syllabus controls

### `NewTactic`, `NewTheorem`, `NewDefinition`
Use these when an item has earned visibility.

Good uses:
- first exposure with clear explanation,
- promotion of a move to stable repertoire,
- explicit marking that “this now matters.”

Bad uses:
- dumping everything in at once,
- unlocking an item before the learner has a reason to care,
- exposing variants that clutter the mental model.

### `Disabled*`, `Only*`
Use these to spotlight the intended toolset for a level.

Good uses:
- keeping search burden down,
- focusing attention on one move family,
- preventing accidental solution via a future tool.

Bad uses:
- using them to create artificial difficulty,
- hiding tools the learner has every reason to expect,
- making the environment feel inconsistent.

### `TheoremTab`
Use theorem tabs to reduce visual search and group theorems by a learner-facing concept rather than by implementation accident.

### `NewHiddenTactic`
Use this for aliases and variants that improve usability without cluttering the visible inventory.

Good uses:
- admitting standard aliases (`rw` / `rewrite`, `rwa`, etc.),
- supporting experienced Lean users quietly,
- keeping the learner-facing inventory small.

Bad uses:
- hiding semantically important tactics that the learner really should understand,
- creating magical behavior the course never explains.

## 3. `Statement` is where the level’s real lesson lives

A level should almost always have:
- a natural-language docstring,
- a precisely scoped statement,
- and a sample proof designed for hint placement and repertoire analysis.

### Named statements
Give a `Statement` a name only if you really want it to become reusable later. Naming everything pollutes the theorem inventory.

### Local `let`
Use local `let` definitions when a level needs a temporary construction. This is excellent for keeping a level self-contained and for introducing local mathematical objects without global noise.

### `preamble`
Use `(preamble := ...)` when the learner should prove the proposition-level content without being distracted by irrelevant data fields or setup mechanics.

## 4. `Hint` is a pedagogy tool, not a spoiler machine

Hints are **context-aware, not history-aware**. That matters.

Good implications:
- place hints at the exact goal state you want to rescue,
- use `Branch` to cover dead ends or alternative proof paths,
- use hidden hints for deeper rescue layers,
- use strict matching when the distinction really matters.

Bad implications:
- assuming hints appear in the order you wrote them,
- writing hints that depend on the user having taken your exact route,
- relying on one linear sample proof to rescue every failure mode.

A good hint should do one of:
- name the next proof obligation,
- suggest the shape of the next move,
- remind the player of a previously learned tool,
- explain why the current state matches that tool,
- or warn against a specific false move.

A weak hint merely gives away the answer.

## 5. `Branch` lets you teach dead ends and alternatives

Use `Branch` when:
- a common wrong path deserves recovery guidance,
- a second proof route is mathematically enlightening,
- or you want hint coverage beyond the mainline proof.

This is essential if you care about learner recovery rather than only about your own preferred proof.

## 6. `Template` / `Hole` are strong medicine

A template can be useful when:
- editor mode is pedagogically important,
- the main lesson is proof structure rather than proof discovery,
- or the syntax burden would otherwise swamp the mathematical lesson.

Avoid templates when:
- they turn the task into slot-filling,
- they remove the need to read the goal state,
- or they deprive the learner of choosing the next move.

Use them sparingly and intentionally.

## 7. Doc entries are part of course quality

`TacticDoc`, `TheoremDoc`, and `DefinitionDoc` should not be afterthoughts.

House standard for docs:
- what the item does,
- exact syntax,
- when to use it,
- one minimal example,
- one common misuse or warning.

If you fail here, players will feel it immediately.

## 8. Images, markdown, LaTeX, and settings are not decoration

Use images and markdown to:
- motivate,
- visualize,
- compress explanation,
- or support transfer to ordinary mathematics.

Use `Settings` to improve readability when the proof state format would otherwise obstruct learning.

Remember that world size and UI behavior matter. If a world is visually unwieldy, the curriculum is paying a cost.


## 8.5 World size is semantic, not numeric

World division is driven entirely by semantic coherence — whether the
levels share a center of gravity — not by level count. A world with 5
levels and a world with 20 levels can both be correctly scoped. The only
valid split triggers are semantic: unrelated theorem families, incoherent
world intro, or cognitive overload from too many new burdens at once.

A world should contain as many levels as the learner needs to master its
topic, including thorough practice, coached retrieval, and fresh surface
transfer. Never suggest a world has “too many levels” as a defect.

## 9. Running locally, updating, and publishing are part of authorship

A good course author knows enough of the technical workflow to preserve learner experience.

That means being able to:
- run and playtest locally,
- update the Lean/toolchain/server pairing,
- repair dev setup drift,
- and publish a new version safely.

A technically broken level is pedagogically broken.
