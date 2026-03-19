# World Author

## Context

You are authoring a complete world for a lean4game course. This is Phase 2a of the course production pipeline.

Read `current-course.txt` for the course directory name.
Read `current-world.txt` for the world you will author. Read the corresponding section of PLAN.md for that world's design spec.
Read `{course}/PLAN.md` for the full course architecture.

## Required mindset

Treat the course as a layered object. Every world must address all five layers:

1. **Syllabus layer** — what mathematics must the learner leave with?
2. **Proof-move layer** — what proof habits and proof shapes must they acquire?
3. **Lean-expression layer** — what commands, syntax, notation, and inventory items must they control?
4. **Example layer** — what concrete objects must the learner have worked with?
5. **Transfer layer** — what should still remain if Lean is removed and only ordinary proof writing remains?

## Non-negotiable behavior

- Never output skeleton Lean code. Write complete code or do not write code yet.
- Never let theorem coverage substitute for proof-move coverage.
- Never let abstract coverage substitute for concrete example coverage.

## CRITICAL CONSTRAINT

You are authoring ONE world: the world named in `current-world.txt`. Do NOT author any other worlds. Do NOT continue to the next world. Do NOT run reviews or audits. Write the files for this one world and stop.

## World authoring — a world is a chapter with a center of gravity

### Step 1: Name the world's promise

Write one sentence: "By the end of this world, the learner will be able to ..."

If you cannot finish that sentence crisply, the world is not scoped yet. Go back to the plan.

### Step 2: Choose the world type

One of: onboarding/tutorial, lecture, pset, example/case-study, review/consolidation.

This choice changes: intro length, level density, hint density, whether new items are allowed, boss expectations.

For proof-heavy mathematical courses, a lecture/pset alternation is a strong default:
- lecture worlds introduce and model
- pset worlds re-cover at lower scaffolding and new surface forms
- example worlds concretize abstract theory on specific objects

Example/case-study worlds are centered on a specific mathematical object (e.g., D₄, S₃, ℤ/6ℤ). Their levels explore different facets of that object. The intro should introduce the object concretely. The boss should integrate multiple facets. New abstract theory should NOT be introduced — the point is to exercise existing theory on concrete ground.

### Step 3: Set granularity

One dominant center per world. **No level count limits.** As many levels as the learner needs. The only valid split triggers are semantic.

**Cognitive load principle**: Always err on the side of splitting rather than risking overload. If a topic has its own center of gravity, it should be its own world.

### Step 4: Design the level ladder

For each level, classify it as one primary type:
- `first-contact` / `definition-in-action` / `proof-move drill` / `notation warning` / `retrieval` / `transfer` / `contrast/misconception` / `concrete-computation` / `counterexample` / `mini-integration` / `boss`

For every level specify:
- **dominant lesson**: one sentence ("This level teaches the learner to ...")
- **novelty budget**: at most ONE new burden (new math, new proof move, new Lean move, or new notation). Everything else should be familiar. The learner has completed NNG4, so basic tactics are baseline. This does not relax as the course progresses.
- **new burdens**: what is novel in this level
- **prior burdens reused**: what familiar moves are expected
- **inventory changes**: NewTactic/NewTheorem/NewDefinition/NewHiddenTactic/DisabledTactic/DisabledTheorem
- **hint philosophy**: use hints in layers: (1) state-reading/strategy hint (visible), (2) tool reminder/route hint, (3) direct rescue hint (hidden). Use `Branch` for common wrong turns.
- **conclusion**: must do at least one of: summarize the reusable recipe, translate to plain math language, explain what was subtle, preview where the move returns. A conclusion that only says "done" is weak.

A strong default lecture-world ladder is:
1. motivation / first contact
2. worked example
3. coached practice
4. second coached practice or contrast case
5. retrieval or mild transfer
6. boss

A strong default pset-world ladder is:
1. re-entry reminder
2. short transfer
3. medium transfer
4. twist / warning case
5. longer integration or mini-boss

**Statement shape**: choose a statement whose surface mathematics makes the dominant lesson visible. Hold everything else constant so the new move is easy to see. For first-contact definitions, pick the simplest theorem whose proof exercises the structure of the definition.

**Sample proof**: write the sample proof for pedagogy, not just correctness. The proof should expose the intended proof shape, support repertoire analysis, and create the right hint trigger points. The proof should be discoverable: a learner who tries things and backtracks should make progress without needing to type more than a short line at a time.

**Doc house standard** for new inventory items:
- what it does
- exact syntax
- when to use it
- one example
- one common misuse or warning

**Template/Hole**: use only if the main lesson is proof structure and the editor is part of the lesson. Avoid when they suppress genuine next-move choice.

**Two-learner test**: For each level, ask: Will the novice know what the level is trying to teach? Will the novice's failure states be recoverable? Will the experienced user be irritated by missing aliases or clutter?

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

Lecture intros may be long if they do real conceptual work. Pset intros should be shorter and more challenge-oriented.

### Step 7: Plan inventory behavior

For each new item: visible or hidden? Doc entry? Theorem tab? Why now?

Use:
- `NewHiddenTactic` for harmless alias support
- `Only*` / `Disabled*` to focus attention
- Named statements only when later reuse is intended

**Critical**: Use only ONE `NewTheorem`/`NewTactic`/`NewDefinition` command per type per level. The GameServer replaces (not appends) on each call. Combine into `NewTheorem foo bar baz`.

### Step 8: Design the boss

A boss should: require several moves seeded earlier, expose weak coverage, produce a "now I see the whole method" moment. Write the boss's dependency chain explicitly: which earlier levels seeded which subskills.

If the boss depends on an unseeded move, redesign the world.

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

