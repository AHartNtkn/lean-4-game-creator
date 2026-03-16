# lean4game-studio-hank

A Hankweave workflow that converts 49 stub lean4game courses into complete, reviewed, playtested courses.

## Quick Start

Hankweave uses the Claude Agent SDK to execute codons. If you are on a Claude Code Max subscription, authenticate by extracting your OAuth token from Claude Code's credential store:

```bash
# Extract your Claude Code OAuth token
export CLAUDE_CODE_OAUTH_TOKEN=$(python3 -c "import json; print(json.load(open('$HOME/.claude/.credentials.json'))['claudeAiOauth']['accessToken'])")
```

Then run from the project root:

```bash
# Validate the hank
bunx hankweave lean4game-studio-hank/hank.json . --validate

# Run the full pipeline
bunx hankweave lean4game-studio-hank/hank.json .

# Smoke test: single world of first course
bunx hankweave lean4game-studio-hank/hank.json . --max-iterations 20
```

**Note:** `bunx` comes with [Bun](https://bun.sh). Install with `curl -fsSL https://bun.sh/install | bash`. You can also use `npx` instead of `bunx` if you prefer Node.

## Architecture

The pipeline is a single flat loop (hankweave doesn't support nested loops) that uses `pipeline-state.json` as a state machine to track progress across three levels of iteration:

1. **Course level** — iterates over 49 courses in prerequisite order
2. **World level** — iterates over worlds within each course's plan
3. **Review level** — iterates review-fix cycles until a world passes or 5 rounds are exhausted

### Pipeline Flow

```
initialize
  │
  ▼
┌─────────────────────────────────────────┐
│ main-pipeline loop (limit: 8000)        │
│                                         │
│  select-course ──► coverage-map         │
│                      │                  │
│                      ▼                  │
│               course-architect          │
│                      │                  │
│                      ▼                  │
│  ┌──► world-author ──► build-and-fix    │
│  │                        │             │
│  │                        ▼             │
│  │    ┌──► enrichment-review            │
│  │    │         │                       │
│  │    │         ▼                       │
│  │    │    playtest-audit               │
│  │    │         │                       │
│  │    │         ▼                       │
│  │    │    review-gate ──┐              │
│  │    │         │     (done)            │
│  │    │    (continue)    │              │
│  │    │         │        ▼              │
│  │    │         ▼   mark-world ─────┐  │
│  │    └── fix-issues                │  │
│  │                      (next world)│  │
│  └──────────────────────────────────┘  │
│                                         │
│  cross-world-coverage                   │
│         │                               │
│         ▼                               │
│  cross-world-fix                        │
│         │                               │
│         ▼                               │
│  mark-course-complete ──► select-course │
│                                         │
└─────────────────────────────────────────┘
```

### State Machine

Each iteration, only ONE codon does real work. The others check `pipeline-state.json` via their rig setup and skip immediately. The active codon updates `pipeline-state.json.nextStep` before finishing, which determines which codon is active in the next iteration.

State transitions are deterministic and local — each codon knows only what comes after itself:

| After | Next Step |
|-------|-----------|
| select-course | coverage-map (or done if all complete) |
| coverage-map | course-architect |
| course-architect | author-world |
| author-world | build (or cross-world-coverage if all worlds done) |
| build | enrichment-review |
| enrichment-review | playtest-audit |
| playtest-audit | review-gate |
| review-gate | fix-issues (continue) or mark-world (done) or halt (abort) |
| fix-issues | enrichment-review (loop back) |
| mark-world | author-world (next world) |
| cross-world-coverage | cross-world-fix |
| cross-world-fix | mark-course |
| mark-course | select-course (next course) |

## How CLAUDE.md Rules Become Structural

| Rule | Structural Encoding |
|------|-------------------|
| FAIL means STOP | Gate codon sets `abort` after 5 failed review cycles → mark-world halts pipeline |
| First reviews never pass | Gate prompt: if reviewRound=1 and both reviews claim PASS, force `continue` |
| One world per agent | Each codon is `continuationMode: fresh`. One world per iteration cycle. |
| Review files are truth | File-mediated communication. No return messages, no memory. |
| Speed is the enemy | Time budgets only (flat-rate Max plan). No cost pressure. |
| Enrichment suggestions implemented | fix-issues prompt: "NEVER reject because too much work" |

## File Layout

```
lean4game-studio-hank/
├── hank.json                         # Workflow definition
├── prompts/
│   ├── initialize.md                 # Pipeline initialization
│   ├── select-course.md              # Course selection (haiku)
│   ├── phase1-coverage-mapper.md     # Coverage mapping (opus)
│   ├── phase1-course-architect.md    # Course design (opus)
│   ├── phase2-world-author.md        # World authoring (opus)
│   ├── phase2-build.md               # Build & fix (opus)
│   ├── phase2-enrichment-reviewer.md # Enrichment review (opus)
│   ├── phase2-playtest-auditor.md    # Playtest audit (opus)
│   ├── phase2-review-gate.md         # Quality gate (opus)
│   ├── phase2-fix-issues.md          # Fix issues (opus)
│   ├── phase2-mark-complete.md       # Mark world done (haiku)
│   ├── phase3-coverage-remap.md      # Cross-world coverage (opus)
│   ├── phase3-cross-world-fix.md     # Cross-world fix (opus)
│   └── mark-course-complete.md       # Course completion (haiku)
├── sentinels/
│   └── quality-watchdog.json         # Quality alert sentinel
└── README.md
```

## State Files

Created at runtime in the execution directory:

| File | Purpose |
|------|---------|
| `pipeline-state.json` | State machine: nextStep, currentCourse, currentWorld, reviewRound, etc. |
| `catalog-progress.json` | Which courses are complete |
| `current-course.txt` | Active course directory name |
| `current-world.txt` | Active world identifier |
| `world-progress.json` | Which worlds are complete in current course |
| `should-run.txt` | Per-codon skip flag (written by rig, read by prompt) |
| `build-log.txt` | Latest build output |
| `sentinel-alerts.txt` | Quality watchdog alerts |
| `{course}/reviews/*.md` | Review artifacts |
| `{course}/reviews/gate-decision.json` | Gate verdicts |

## Verification

```bash
# 1. Schema validation
bunx hankweave lean4game-studio-hank/hank.json . --validate

# 2. Single-world smoke test (set --max-iterations low)
bunx hankweave lean4game-studio-hank/hank.json . --max-iterations 20

# 3. FAIL injection test
# After smoke test, manually inject a P0 defect and re-run
# Verify gate sets continue, fix-issues attempts fix, pipeline converges or aborts

# 4. Full single-course test
bunx hankweave lean4game-studio-hank/hank.json . --max-iterations 500

# 5. Multi-course test
bunx hankweave lean4game-studio-hank/hank.json . --max-iterations 2000
```

## Cost

**Harness**: Claude Code (Max plan — flat rate). All codons execute inside Claude Code sessions.

- No per-token cost. Budgets use `maxTimeSeconds`.
- The `model` field controls which model Claude Code uses.
- Each skipped codon takes ~30-60 seconds (reads flag, writes SKIPPED).
- Each active codon takes 5-90 minutes depending on complexity.
- Estimated per-course wall time: 12-48 hours.
- Estimated total pipeline time: ~1000-2000 hours (weeks of continuous runtime).

## Design Decisions

1. **No pattern miner**: All 49 courses are stubs. Reference documents serve as style authority.
2. **No nested loops**: Hankweave constraint. Single flat loop with state machine workaround.
3. **No conditional termination**: Codons skip via flag file when inactive. Costs ~30s per skip on flat-rate plan.
4. **Sequential reviews**: Enrichment and playtest run as separate codons (not parallel). Preserves fresh-eyes property.
5. **Gate is read-only**: Structural separation prevents rationalization.
6. **Stuck world = halt**: 5 failed review rounds → pipeline stops. Human must intervene.
7. **Commit per course**: Incremental progress saved via git after each course passes.
