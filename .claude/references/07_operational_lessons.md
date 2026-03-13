# Operational lessons from authoring

Concrete patterns learned during authoring that the higher-level reference
files do not cover. These are not project-specific — they apply to any
lean4game course.

## Hint design

- **Layer hints**: Strategy hint (visible) first, then code template (hidden).
  First hint should describe the strategy, not give the code.
- **Both paths need hints**: If a `Branch` alternative exists, it needs its
  own hints at every tactic step — not just the primary path.
- **calc hints misfire**: Hints inside a `calc` step's `:= by` fire after the
  learner already wrote the correct intermediate expression. The hard part
  (choosing the intermediate expression) gets no hint. Fix: add a top-level
  hidden hint showing the full calc plan.
- **Branch limitations**: Branches must contain complete proofs. A Branch
  that catches a wrong move but can't lead to a valid proof (dead end)
  cannot use `sorry` — it simply can't be added.

## Coverage closure

- Every boss subskill must be introduced AND practiced before the boss.
- `← rw` (reverse rewriting) is a separate skill from forward rewriting —
  teach it explicitly before requiring it.
- Explicit arguments to `rw [lemma a b c]` is a separate skill from bare
  `rw [lemma]` — teach before requiring.
- Partial explicit args `rw [lemma a]` is different from full
  `rw [lemma a b c]` — don't assume transfer between them.
- Add a coaching level before the boss for any move the boss uses for the
  first time in combination.

## Boss design

- Boss integrates, never introduces.
- Multiple proof paths are good but ALL paths need hint coverage.
- Scale surprise check: does the boss require a longer proof than anything
  practiced? If so, add a coaching level.
- Pset bosses need 5+ integrated moves — a 2-move boss is too easy.

## Pset design

- Don't clone lecture levels as pset levels — use genuinely fresh surface
  forms.
- Never use untaught API (e.g. `.mpr`) — decompose into taught moves
  (`rw` + `exact`).
- Multi-rewrite chains (`rw [a, b, c, d]`) are interactive-hostile: the
  learner must type the entire chain correctly before anything happens.
  Break into individual `rw` steps with a hint after each step.

## Inventory DSL behavior

- **One `NewTheorem`/`NewTactic`/`NewDefinition` per type per level**: The
  GameServer replaces (not appends) the item list on each call. A second
  `NewTheorem` silently overwrites the first. Combine into
  `NewTheorem foo bar baz`. Different types on separate lines are fine.
- `TacticDoc` must appear before `DisabledTactic` in same file.
- `group` tactic pattern: introduce, then disable in next world (not same
  world's boss) — cleaner pedagogy.
- Free theorems (NewTheorem without proving) need justification — prefer a
  level if the theorem is important enough to appear in the boss.

## Tactic gating

- All NNG4-prerequisite tactics (rw, exact, apply, intro, cases,
  constructor, assumption, have, use) must be available from the start.
  The game can *teach* them at specific points, but should never *block*
  them without a clear pedagogical reason.
- Tactics that ARE fine to delay: `simp`, `group`, `decide`, and
  mathlib-specific tactics (omega, norm_num, ring, aesop).
- When a new tactic is taught, disable it for subsequent first-contact
  levels of NEW concepts to force manual engagement, then re-enable when
  the lesson is explicitly about combining the tactic with the new concept.

## Lean 4 rw behavior

- `rw [h]` replaces ALL occurrences of the pattern, not just the first.
- In calc blocks, use FORWARD rewrites (simplifying direction).
  Backward `←` rewrites risk the all-occurrences problem.
- When `← rw` is necessary, provide the explicit argument to limit matching.

## lean4game server limitations

- **`open scoped` doesn't work for players**: The game server's
  `RpcHandlers.lean` doesn't apply the level's saved scope to the
  interactive proof environment. `open scoped Pointwise` (or any scoped
  instance) in level files compiles fine with `lake build` but is invisible
  to players. Fix: use `attribute [instance] Set.smulSet` (or the relevant
  instance) in `Game/Metadata.lean` to permanently activate it.
- When adding new scoped notation or instances, always activate them via
  `attribute [instance]` in Metadata.lean, not via `open scoped` in level
  files.

## File management

- When inserting a new level, rename files to keep `L{NN}` prefix matching
  `Level N`. Rename from highest number down to avoid collisions:
  L08→L09, L07→L08, then create L07. Update Level numbers inside renamed
  files and the world base file's imports.
