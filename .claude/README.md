# lean4game-studio

A skill pack for building **good** lean4game courses: games with complete coverage, sane granularity, strong pedagogy, tight proof-move sequencing, and a maintenance loop that keeps the course coherent as it grows.

This pack is not a thin wrapper around lean4game documentation. It assumes the docs exist. Its job is to teach judgment:

- what to cover,
- in what order,
- at what granularity,
- with what kind of level,
- with what kind of hint,
- and how to detect when a technically correct level is still pedagogically wrong.

## What this pack optimizes for

1. **Teaching the how, not just the what.**  
   A lean4game level is not mainly about the theorem statement. It is about the proof move, the reading of the goal state, the choice of witness, the use of a definition, the recognition of a proof shape, and the transfer of that move to fresh surface forms.

2. **Coverage closure.**  
   Every high-value concept and proof move should be tracked across first exposure, supported use, unsupported retrieval, integration, and transfer. A course is incomplete if it merely mentions a theorem once.

3. **Good granularity.**  
   Levels should be small enough to isolate real subskills, but large enough to teach reusable proof moves. Worlds should feel like coherent chapters, not random bags of exercises. Bosses should integrate a repertoire, not replay one trick.

4. **Actual course structure.**  
   The pack is shaped by the patterns visible in NNG4 and RealAnalysisGame: explicit world arcs, inventory gating, strong intros and conclusions, lecture/pset alternation, and boss levels that consolidate a family of moves.

5. **Maintenance as pedagogy.**  
   Missing doc entries, missing aliases, drifting dependencies, and toolchain breakage all damage learning. Maintenance is part of course quality, not an afterthought.

## Contents

### Skills
- `lean4game-studio`: front-door orchestrator
- `lean4game-pattern-miner`: infer house style and hidden constraints from an existing repo
- `lean4game-coverage-mapper`: build and audit coverage/granularity maps
- `lean4game-course-architect`: design the course arc and world graph
- `lean4game-world-author`: design or write a full world
- `lean4game-level-author`: design or write a single level
- `lean4game-playtest-auditor`: red-team levels/worlds/games for pedagogy and technical fit
- `lean4game-maintainer`: update, expand, refactor, and publish without course drift

### Agents
- `style_miner.md`
- `novice_playtester.md`
- `pedagogy_grader.md`
- `progression_analyzer.md`
- `blind_comparator.md`

### Commands
- `repo-xray.md`
- `coverage-map.md`
- `game-plan.md`
- `draft-world.md`
- `draft-level.md`
- `expand-game.md`
- `playtest.md`
- `maintenance-pass.md`
- `compare-two-versions.md`

### References
- `00_what_good_looks_like.md`
- `01_patterns_from_existing_games.md`
- `02_technical_levers.md`
- `03_quality_rubric.md`
- `04_failure_taxonomy.md`
- `05_coverage_and_granularity.md`
- `06_source_basis.md`

### Evals
- `evals/evals.json` contains realistic benchmark prompts for the full pack.

## Suggested use

### New game from scratch
1. Run `coverage-map`
2. Run `game-plan`
3. Use `draft-world`
4. Use `draft-level` for difficult or flagship levels
5. Run `playtest`
6. Use `compare-two-versions` whenever you have competing drafts

### Existing game, expansion or repair
1. Run `repo-xray`
2. Run `coverage-map`
3. Run `expand-game` or `maintenance-pass`
4. Run `playtest`
5. Use `compare-two-versions` for contentious redesigns

## Non-negotiables

- Never dump commands into the inventory without a teaching reason.
- Never treat theorem coverage as enough; track proof-move coverage.
- Never let a boss demand an untaught micro-skill.
- Never let a world become so broad that the learner cannot state what its central move was.
- Never make psets into clones of lecture examples.
- Never trust compilation alone as evidence that a level is good.
- Never ship a change without checking whether it improved or worsened coverage, granularity, and learner recovery.

## Quality loop

The intended loop is:

1. infer local style,
2. map coverage,
3. plan the course arc,
4. author a world or level,
5. simulate a learner,
6. grade against the rubric,
7. compare alternatives blindly,
8. patch,
9. only then merge or publish.

This is the same spirit as the attached skill-creator guidance: outcome first, eval loop first, then iteration.
