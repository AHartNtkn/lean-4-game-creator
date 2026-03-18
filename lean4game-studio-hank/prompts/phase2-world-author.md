# World Author

## Context

You are authoring a complete world for a lean4game course. This is Phase 2a of the course production pipeline.

Read `current-course.txt` for the course directory name.
Read `current-world.txt` for the world you will author. Read the corresponding section of PLAN.md for that world's design spec.
Read `{course}/PLAN.md` for the full course architecture.

## World authoring — a world is a chapter with a center of gravity

### Step 1: Name the world's promise

Write one sentence: "By the end of this world, the learner will be able to ..."

If you cannot finish that sentence crisply, the world is not scoped yet. Go back to the plan.

### Step 2: Choose the world type

One of: onboarding/tutorial, lecture, pset, example/case-study, review/consolidation.

This choice changes: intro length, level density, hint density, whether new items are allowed, boss expectations.

### Step 3: Set granularity

One dominant center per world. **No level count limits.** As many levels as the learner needs. The only valid split triggers are semantic.

**Cognitive load principle**: Always err on the side of splitting rather than risking overload. If a topic has its own center of gravity, it should be its own world.

### Step 4: Design the level ladder

For each level, specify:
- **type**: intro / worked-example / coached-practice / retrieval / transfer / warning / boss
- **dominant lesson**: one sentence
- **new burdens**: what is novel in this level
- **prior burdens reused**: what familiar moves are expected
- **inventory changes**: NewTactic/NewTheorem/NewDefinition/NewHiddenTactic/DisabledTactic/DisabledTheorem
- **hint philosophy**: what layers of hints are needed
- **conclusion**: what the conclusion should say

### Step 4b: Verify no level is exploitable

For each level, check:
- **Unconstrained return type**: `Subgroup G`, `Nat`, etc. can be solved with `exact ⊥`/`exact 0`. Fix: wrap in `∃ H, H.carrier = {g | P g}` or similar.
- **Library one-shot**: If the statement matches a Mathlib lemma, `exact that_lemma` bypasses it. Fix: `DisabledTheorem`.
- **Automation one-shot**: If `simp`/`decide`/`group` closes the goal, it teaches nothing. Fix: `DisabledTactic`.
- **Common tactic exploits**: `fin_cases`, `ext`, `interval_cases`, `by_cases` — disable per-level as needed.
- **Common theorem exploits on Fin**: `Fin.forall_fin_two`, `Fin.forall_fin_one`, `Subsingleton.elim`, `Unique.eq_default`.
- **Lattice alias exploits**: Finset ∪/∩/\ are lattice ⊔/⊓/\, so Finset identities have lattice-level aliases (`sup_comm`, `inf_le_left`, `le_antisymm+sup_le`, `sup_eq_left`, etc.) that MUST ALSO be disabled.

### Step 4c: Verify proofs are interactive

Each level's proof must be a sequence of discrete tactic steps where each step can be typed independently and produces visible goal state change. Red flags:
- Elaborate one-liners (`refine ⟨{ field := ..., ... }, rfl⟩`)
- Opaque goals (set-membership notation instead of concrete predicate)
- Bundled rewrites (`rw [a, b, c, d, e]` — break into individual steps in early levels)

### Step 5: Plan coverage closure

List the world's core items and show how each gets: introduction, supported use, retrieval, boss integration.

### Step 6: Write the world intro

Must do at least one of: motivate the theorem family, tell a historical/conceptual story, preview the proof shape, warn about the main trap.

### Step 7: Plan inventory behavior

For each new item: visible or hidden? Doc entry? Theorem tab? Why now?

**Critical**: Use only ONE `NewTheorem`/`NewTactic`/`NewDefinition` command per type per level. The GameServer replaces (not appends) on each call. Combine into `NewTheorem foo bar baz`.

### Step 8: Design the boss

A boss should: require several moves seeded earlier, expose weak coverage, produce a "now I see the whole method" moment. Write the boss's dependency chain explicitly.

### Step 9: Write the code

Produce COMPLETE files:
- World file (with intro, imports, world declaration)
- All level files (complete Lean code with Statement, hints, docstrings, inventory commands)
- Game.lean updates (imports and dependencies)

**Never produce stubs.** Every level must have complete, compilable code.

## Operational rules for code

- DisabledTactic baseline: `trivial decide native_decide simp aesop simp_all`
- `norm_num` and `linarith` are pervasive exploits — disable per-level when teaching manual reasoning
- `tauto` closes many propositional goals — disable when teaching logic
- Hint strings must NOT use `{curly braces}` (GameServer parses as interpolation)
- `show`/`change` are GameServer keywords — use `«show»`/`«change»` for TacticDoc
- `NewHiddenTheorem` does not exist — only `NewHiddenTactic`
- `TacticDoc` must appear before `DisabledTactic` in the same file
- `open scoped` doesn't work for players — use `attribute [instance]` in Metadata.lean

## Output files

Write all files to the course directory:
- `{course}/Game/Levels/{WorldName}/*.lean` — level files
- `{course}/Game/Levels/{WorldName}.lean` — world base file
- Update `{course}/Game.lean` — add imports and dependencies

