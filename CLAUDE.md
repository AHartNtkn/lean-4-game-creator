# lean_worlds Project Instructions

## YOU ARE CALLED BY A SCRIPT

You are invoked by `run.sh` via `claude -p` or `codex exec`. Each invocation gives you ONE task via a prompt. Do that task and stop.

**Do NOT:**
- Spawn subagents
- Use the Agent tool
- Continue to the next phase of the pipeline
- Author multiple worlds
- Run reviews after authoring
- Run the full pipeline yourself

The bash script handles all orchestration, looping, and sequencing. You do ONE thing per invocation.

## Quality rules

These apply to every invocation regardless of task:

- **Never output skeleton code.** Write complete, compilable code or don't write code yet.
- **Never let theorem coverage substitute for proof-move coverage.**
- **Never let abstract coverage substitute for concrete example coverage.**
- Hint strings must NOT use `{curly braces}` (GameServer interpolation).
- `show`/`change` are GameServer keywords — use `«show»`/`«change»` for TacticDoc.
- `NewHiddenTheorem` does not exist — only `NewHiddenTactic`.
- Use only ONE `NewTheorem`/`NewTactic`/`NewDefinition` per type per level (GameServer replaces, not appends).
- `TacticDoc` must appear before `DisabledTactic` in the same file.
- `open scoped` doesn't work for players — use `attribute [instance]` in Metadata.lean.
- DisabledTactic baseline: `trivial decide native_decide simp aesop simp_all`

## Operational lessons

- `norm_num` and `linarith` are pervasive exploits — disable per-level when teaching manual reasoning.
- `tauto` closes many propositional goals — disable when teaching logic.
- `fin_cases`, `ext`, `interval_cases`, `by_cases` are common tactic exploits to disable.
- `Fin.forall_fin_two`, `Fin.forall_fin_one`, `Subsingleton.elim`, `Unique.eq_default` are common theorem exploits on Fin levels.
- **Lattice aliases are a major exploit vector** — Finset ∪/∩/\ are lattice ⊔/⊓/\, so every Finset identity has lattice-level aliases (sup_comm, inf_le_left, le_antisymm+sup_le, sup_eq_left, etc.) that must ALSO be disabled.
- Hints inside `calc` steps fire after the learner already wrote the correct intermediate expression. Add top-level hidden hints showing the full calc plan.
- `Branch` must contain complete proofs — no `sorry`.
- `← rw` (reverse rewriting) is a separate skill from forward rewriting — teach explicitly.
- Explicit arguments to `rw [lemma a b c]` is a separate skill from bare `rw [lemma]`.
- Boss integrates, never introduces. All boss moves must be seeded in prior levels.
- Pset boss needs 5+ integrated moves.
- Multi-rewrite chains (`rw [a, b, c, d]`) are interactive-hostile — break into individual steps.
- When inserting a new level, rename files from highest number down to avoid collisions.
