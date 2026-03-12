---
name: lean4game-pattern-miner
description: Use this when the user provides an existing lean4game repo, world, or level set and wants to extend, repair, or imitate it. This skill infers the game’s real house style, coverage logic, granularity choices, boss structure, hint style, and inventory policy so later edits do not create pedagogical style drift.
---

# lean4game-pattern-miner

Your job is to infer the course’s **actual design logic** from the repo, not to impose your own favorite style.

Read:
- `references/01_patterns_from_existing_games.md`
- `references/05_coverage_and_granularity.md`
- `references/04_failure_taxonomy.md`

## What to inspect

Inspect at least these layers:

1. `Game.lean`
   - world order
   - dependency edges
   - title-screen promise
   - visible course arc

2. world files
   - lecture vs pset vs onboarding vs review
   - world introductions
   - average number of levels
   - boss placement

3. representative levels
   - first-use levels for important tactics/definitions
   - one boss level
   - one pset level
   - one advanced lecture level

4. docs and inventory
   - `TacticDoc`, `TheoremDoc`, `DefinitionDoc`
   - naming conventions
   - theorem tabs
   - hidden aliases / variants

5. user-facing friction
   - issues, complaints, or repo notes
   - places where docs or aliases are likely missing
   - style inconsistencies

## Infer the style map

Produce a **style map** containing:

- target learner profile
- narrative voice
- typical intro length
- typical conclusion behavior
- world archetypes
- level archetypes
- how new tactics/definitions are introduced
- hint density and hint tone
- whether psets are terse or explanatory
- what makes a boss in this repo
- whether the course prioritizes paper-proof transfer
- how much tolerance the repo has for expert aliases
- local notation conventions
- dependency philosophy
- world-size norms

## Infer the hidden curriculum

Find the repo’s hidden rules, such as:

- “lecture worlds explain strategy explicitly”
- “psets are short and mostly transfer-oriented”
- “boss levels recap the world’s tactics”
- “new notation gets its own warning”
- “docstrings are long and motivational”
- “theorems become inventory only when they will be reused”
- “inventory is kept learner-facing, while aliases stay hidden”

These are the rules future edits must preserve unless the user explicitly wants a redesign.

## Infer coverage logic

Do not stop at style. Infer how the repo chooses what to cover:

- by course syllabus?
- by theorem family?
- by proof-move cluster?
- by tactic repertoire?
- by historical narrative?
- by mixed lecture/pset rhythm?

Then say how finely the repo cuts material:
- too coarse,
- appropriate,
- or too fine.

## Output format

Return these sections:

1. **House style summary**
2. **Coverage logic**
3. **Granularity logic**
4. **World archetypes**
5. **Boss formula**
6. **Inventory policy**
7. **Hint policy**
8. **Likely learner pain points**
9. **Constraints future contributors must preserve**
10. **Places where the repo itself should probably be refactored**

## Red flags to detect

- worlds that became too large
- missing or thin docs for major inventory items
- dependencies that no longer reflect conceptual prerequisites
- a pset sequence that became clone-heavy
- a world where the intro promises something the levels do not deliver
- expert-hostile alias gaps
- sharp shifts in narrative voice or level granularity

A good pattern miner is conservative about style drift and aggressive about diagnosing hidden structural problems.
