# lean4game-studio

A [Claude Code](https://claude.ai/claude-code) skill pack for building **pedagogically sound** [lean4game](https://adam.math.hhu.de/) courses. It ships as a `.claude/` directory containing skills, agents, commands, and reference documents that guide Claude through course design, level authoring, adversarial playtesting, and ongoing maintenance.

The Group Theory Game in this repo is a working example built entirely using the skill pack.

## What the skill pack does

Most lean4game authoring advice stops at "make sure it compiles." This pack goes further. It tracks:

- **Coverage closure** across five layers: first exposure, supported use, unsupported retrieval, integration, and transfer. A theorem mentioned once is not "covered."
- **Proof-move granularity**, not just theorem granularity. A level's dominant lesson is the move (rewriting right-to-left, choosing a witness, recognizing an `apply` shape), not the theorem statement.
- **Inventory gating**. Tactics and theorems are introduced, practiced, and retrieved in a controlled sequence. Nothing appears in the inventory without a teaching reason.
- **Boss integrity**. Boss levels integrate previously practiced skills. They never demand an untaught micro-skill.
- **Hint layering**. Strategy hints come first (visible), code templates come second (hidden). Every `Branch` path gets its own hints.

## Quick start

### Prerequisites

- [Claude Code](https://claude.ai/claude-code) CLI
- A lean4game repo (or create one from the [lean4game template](https://github.com/leanprover-community/lean4game))

### Setup

Copy the `.claude/` directory into your lean4game repository root. The skills, agents, commands, and references will be available to Claude Code automatically.

### Creating a new course

Start Claude Code in **plan mode** (`/plan`). Plan mode is important: course creation is a long-running conversation, and the plan is the mechanism for persisting state across context compactions.

Example starting prompt:

```
Hello. The purpose of this session is to make a group theory world for
lean4game. Please follow the lean4game studio skills. Use the mathlib group
theory formalization files when considering what to and to not include. The
goal is essentially full coverage; we are making a full course, including
advanced topics.
```

Replace "group theory" with your topic. The `lean4game-studio` skill will orchestrate the workflow: coverage mapping, course architecture, world authoring, playtesting, and iteration.

### Tips for long sessions

- **You may need to remind Claude to use the lean4game studio skill** after one or more context compactions. If Claude stops following the studio workflow, tell it to re-engage the skill.
- **Compact before starting a new world** to minimize the chance of compaction happening mid-review. A world design + authoring + audit cycle is the natural unit of work; starting it with a fresh context window reduces interruptions. Following compaction directly with "Good. Implement World X. Make sure to actually follow the lean4game studio skill." increases reliability.
- **CLAUDE.md**: The CLAUDE.md file is constructed to make using the skill more reliable, including injecting the main skill into that file.
- **Expense Note**: World planning and implementation on high reasoning, which was used for the example course, took 30-60 minutes per world.

## Skill pack contents

### Skills (`.claude/skills/`)

| Skill | Purpose |
|---|---|
| `lean4game-studio` | Front-door orchestrator. Routes work through the full pipeline. |
| `lean4game-coverage-mapper` | Builds coverage maps across syllabus, proof-move, Lean-expression, and transfer layers. |
| `lean4game-course-architect` | Designs world graphs, coverage plans, inventory release plans, and boss maps. |
| `lean4game-pattern-miner` | Infers house style, granularity choices, and inventory policy from an existing repo. |
| `lean4game-world-author` | Designs a complete world: level ladder, coverage closure, intro/conclusion, boss structure. |
| `lean4game-level-author` | Designs a single level: dominant lesson, novelty budget, hints, inventory behavior. |
| `lean4game-playtest-auditor` | Red-teams content for coverage gaps, recoverability failures, boss integrity, and technical fit. |
| `lean4game-enrichment-reviewer` | Finds ambitious improvements the auditor wouldn't flag: derivable axioms, missing examples, cross-world foreshadowing. |
| `lean4game-maintainer` | Handles expansion, toolchain updates, and publication without course drift. |

### Agents (`.claude/agents/`)

| Agent | Role |
|---|---|
| `novice_playtester` | Simulates an attentive new learner |
| `pedagogy_grader` | Grades levels against the quality rubric |
| `progression_analyzer` | Analyzes learning progression across a world |
| `style_miner` | Infers design patterns and house style from existing content |
| `blind_comparator` | Compares alternative designs without seeing author context |

### Commands (`.claude/commands/`)

| Command | Use |
|---|---|
| `/repo-xray` | Analyze an existing repo's structure |
| `/coverage-map` | Build and audit coverage/granularity maps |
| `/game-plan` | Design the course arc and world graph |
| `/draft-world` | Design or write a full world |
| `/draft-level` | Design or write a single level |
| `/expand-game` | Add content to an existing game |
| `/playtest` | Run adversarial playtesting |
| `/maintenance-pass` | Update, refactor, or expand without drift |
| `/compare-two-versions` | Compare alternative designs blindly |

### References (`.claude/references/`)

Seven foundational documents covering quality standards, patterns from NNG4 and RealAnalysisGame, the lean4game DSL, a quality rubric, a failure taxonomy, coverage/granularity theory, and source material justification.

## Example: Group Theory Game

The `Game/` directory contains a group theory course built with this skill pack.

### Building the example

```bash
# Requires Lean 4 (see lean-toolchain for exact version)
lake update -R
lake build
```

## Quality loop

The intended authoring loop is:

1. Infer local style (if extending an existing game)
2. Map coverage
3. Plan the course arc
4. Design a world (level ladder, coverage closure, inventory, boss)
5. Write the code
6. Build and fix compilation errors
7. Run the enrichment reviewer (find ambitious improvements)
8. Run the playtest auditor (adversarial red-team)
9. Fix issues, rebuild, re-audit until passing
10. Move to the next world

## License

The skill pack (`.claude/` directory) and the game content (`Game/` directory) are provided as-is for educational use.
