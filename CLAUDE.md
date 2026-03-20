# lean_worlds Project Instructions

## HOW THIS PROJECT WORKS

This project uses a bash script (`lean4game-studio-hank/run.sh`) to orchestrate course authoring. Each step calls `claude -p` (or `codex exec`) with a focused prompt from `lean4game-studio-hank/prompts/`. The script handles all looping, course/world selection, state tracking, and review cycles.

**If you are being called by the script**: you receive ONE task via the prompt. Do that task. Do not do anything else. Do not spawn subagents. Do not run the full pipeline. Do not author multiple worlds. Do not run reviews unless the prompt tells you to review.

**If you are in an interactive session**: the `.claude/commands/` slash commands are available for manual use.

## QUALITY RULES (apply to all contexts)

### One world at a time
Never author, review, or fix multiple worlds in a single session. Each world gets full attention.

### First reviews never pass
A world's first review will always find issues. If a first review claims PASS, investigate — it's a bug in the review process.

### FAIL means STOP
If a review says FAIL, do not move on. Fix the issues and re-review. P0 means blocking. There is no "P0 but close enough."

### No rushing
Quality per world is the only metric. Do not optimize for speed or throughput.

### Enrichment suggestions carry weight
The only valid reason to reject an enrichment suggestion is that implementing it would make the world pedagogically worse. "Too much work" is not valid.

## OPERATIONAL LESSONS

- DisabledTactic baseline: `trivial decide native_decide simp aesop simp_all`
- `norm_num` and `linarith` are pervasive exploits — disable per-level
- `tauto` closes many propositional goals — disable when teaching logic
- Library lemmas one-shot many levels — use `DisabledTheorem`
- Lattice aliases are a major exploit vector — Finset ∪/∩/\ are lattice ⊔/⊓/\, so Finset identities have lattice-level aliases that must ALSO be disabled
- Hint strings: avoid `{...}` (parsed as interpolation by GameServer)
- `show`/`change` are keywords: need `«show»`/`«change»` for TacticDoc
- `NewHiddenTheorem` does not exist — only `NewHiddenTactic`
- `TacticDoc` must appear before `DisabledTactic` in same file
- `open scoped` doesn't work for players — use `attribute [instance]` in Metadata.lean
- `fin_cases`, `ext`, `interval_cases`, `by_cases` are common tactic exploits to disable
- One `NewTheorem`/`NewTactic`/`NewDefinition` per type per level — GameServer replaces on each call
- When inserting levels, rename from highest number down to avoid collisions

## REFERENCE FILES

The `.claude/references/` directory contains pedagogical reference material:
- `00_what_good_looks_like.md` — what good authorship means
- `01_patterns_from_existing_games.md` — patterns from NNG4 and RealAnalysisGame
- `02_technical_levers.md` — lean4game technical mechanisms and their pedagogical use
- `03_quality_rubric.md` — 9-category 0-4 scoring rubric
- `04_failure_taxonomy.md` — 16 failure patterns for correct-but-bad content
- `05_coverage_and_granularity.md` — coverage axes, granularity scales, novelty budgets
- `06_source_basis.md` — what this system was built from
- `07_operational_lessons.md` — concrete patterns from authoring experience

These are read by the automated prompts via `appendSystemPromptFile` or direct file reads.
