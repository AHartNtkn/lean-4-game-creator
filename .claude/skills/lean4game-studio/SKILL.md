---
name: lean4game-studio
description: Use this skill for any task involving the creation, expansion, auditing, or maintenance of a lean4game game or course. This is the front door. It routes the work through coverage mapping, course architecture, authoring, playtesting, and maintenance so the result is a genuinely good course rather than a technically valid repo.
---

# lean4game-studio

You are building or modifying a **course**, not merely a Lean repository.

Read these first:
- `references/00_what_good_looks_like.md`
- `references/01_patterns_from_existing_games.md`
- `references/05_coverage_and_granularity.md`

## Workflow

### Phase 0: Establish style authority

Before any authoring can happen, you need a style authority — a source of truth for how this course makes its pedagogical choices.

**If the repo was written by someone else** (or inherited from a previous session with no design artifacts):
- Run `lean4game-pattern-miner` to infer the house style.
- Run `lean4game-coverage-mapper` to map what's already taught and find gaps.
- The pattern miner's output becomes your style authority.

**If you are building from scratch or continuing work you started**:
- You are the style authority. Your course-architect output, or the design decisions you made when authoring earlier worlds, are the source of truth.
- Do not run the pattern miner on your own output.

### Phase 1: Course design

Run once at the start of a new course. Skip if the course architecture already exists.

1. `lean4game-coverage-mapper` — establish what the course must cover across all five layers (syllabus, proof-move, Lean-expression, example, transfer).
2. `lean4game-course-architect` — design the world graph, granularity plan, inventory release plan, boss map, and transfer plan.

The course architect's output is the plan that governs all subsequent phases.

### Phase 2: World authoring

Run for each world in sequence.

1. `lean4game-world-author` — design the world: level ladder, coverage closure, inventory changes, boss, intro/conclusion.
2. Write the code: world file, level files, Game.lean updates.
3. `lake build` — verify compilation.
4. `lean4game-enrichment-reviewer` — find ambitious improvements the auditor would miss (derivable results, missing examples, unnamed strategies, cross-world opportunities). Incorporate suggestions before auditing. See **Enrichment advice policy** below.
5. `lean4game-playtest-auditor` — red-team the world for coverage, granularity, recoverability, and learner simulation.
6. Fix issues found in the audit.
7. Rebuild and re-audit until the world passes.

### Phase 3: Cross-world review

Run after completing a block of worlds (e.g., after finishing all lecture+pset pairs in a phase of the plan).

1. `lean4game-coverage-mapper` — re-map coverage to check for drift, gaps, or redundancy that emerged during authoring.
2. Patch any issues found.

### Phase 4: Maintenance

Run when the task is fixing bugs, updating toolchain, expanding an existing course, or responding to user feedback.

1. If style is unknown: `lean4game-pattern-miner` first.
2. `lean4game-coverage-mapper` — assess the current state.
3. `lean4game-maintainer` — plan and execute the maintenance work.
4. `lean4game-playtest-auditor` — verify the changes didn't break learner experience.

## Execution model: use subagents

**Every skill invocation in this workflow must be delegated to a subagent** (via the Agent tool). This is not optional. The reason: a subagent starts with a clean context and follows the skill's instructions without bias from prior decisions made in the parent conversation. The parent agent has already committed to design choices, seen its own output, and built up confirmation bias. A subagent evaluating coverage, auditing quality, or designing a world will produce more honest results because it has no stake in defending earlier work.

Concretely:
- When running `lean4game-coverage-mapper`, spawn a subagent with the skill text and the current repo state.
- When running `lean4game-course-architect`, spawn a subagent.
- When running `lean4game-world-author`, spawn a subagent with the world's plan context.
- When running `lean4game-enrichment-reviewer`, spawn a subagent — fresh eyes catch opportunities that the author's tunnel vision misses.
- When running `lean4game-playtest-auditor`, spawn a subagent — this is especially critical since the auditor must be adversarial to the author.
- When running `lean4game-pattern-miner` or `lean4game-maintainer`, spawn a subagent.

The parent agent coordinates, provides context, and integrates results. The subagents do the actual skill work.

**HARD RULE: One world per agent call.** Every world-author, enrichment-reviewer, and playtest-auditor agent must target exactly one world. Never combine two or more worlds into a single agent call. This is non-negotiable — combining worlds degrades the skill invocation, pollutes context, and produces garbage.

## Enrichment advice policy

The enrichment reviewer exists to push the world closer to ideal. Its suggestions are not decorative — they identify real gaps. The only valid reason to reject a suggestion is that implementing it would make the world *less* ideal (e.g., it introduces a pedagogical regression, contradicts the plan, or is factually wrong about the mathlib API).

**You must NEVER reject an enrichment suggestion because:**
- It would make the world "too big" or you want to "keep things lean"
- The change would be "too large" (e.g., splitting a world, adding multiple levels, restructuring the level ladder)
- You want to minimize effort or avoid rework
- The world "already works" or "compiles fine"

**The only standard is: does the change bring the world closer to ideal?** If yes, implement it. Size of change is irrelevant. A world that needs splitting should be split. A world that needs three extra levels should get them. The goal is the best possible course, not the smallest diff.

## Non-negotiable behavior

- Never answer with a doc dump.
- Never plan content without a coverage map.
- Never author content without knowing local house style — but "knowing" means having established it or having mined it, not re-mining your own recent output.
- Never call a draft "good" without checking coverage and granularity.
- Never let theorem coverage substitute for proof-move coverage.
- Never let abstract coverage substitute for concrete example coverage.
- Never ignore pset/review structure; transfer matters.
- Never output skeleton Lean code. If asked for code, write complete code or do not write code yet.

## Required mindset

Treat the course as a layered object:

1. **syllabus layer**
   What mathematics must the learner leave with?

2. **proof-move layer**
   What proof habits and proof shapes must they acquire?

3. **Lean-expression layer**
   What commands, syntax, notation, and inventory items must they control?

4. **example layer**
   What concrete objects must the learner have worked with? Which definitions
   have been concretized, and which counterexamples have been seen? Examples
   can and should be revisited as new theory becomes available — the same
   object through a different theoretical lens is not redundancy. There is
   no budget for examples; if one would enrich the learner, include it.

5. **transfer layer**
   What should still remain if Lean is removed and only ordinary proof writing remains?

A good answer covers all five.

## Required outputs

At the end of any nontrivial task, produce enough of the following to make the work inspectable:

- what is being covered,
- what granularity choices were made,
- what style constraints were applied (and whether they were inferred or established),
- what new inventory items were introduced or withheld,
- where the main proof moves are taught,
- where concrete examples and counterexamples appear,
- where transfer happens,
- what risks remain,
- and what should be playtested next.

If those are missing, the work is not done.
