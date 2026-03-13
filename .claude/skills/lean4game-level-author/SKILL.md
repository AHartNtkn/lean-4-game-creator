---
name: lean4game-level-author
description: Use this when the user wants to design, rewrite, or author a single lean4game level. This skill chooses the level’s dominant lesson, novelty budget, statement shape, docstring, hints, inventory behavior, proof template policy, and conclusion so the level teaches a reusable move instead of merely hosting a theorem.
---

# lean4game-level-author

The unit of level design is not the theorem. It is the **dominant lesson**.

Read:
- `references/02_technical_levers.md`
- `references/05_coverage_and_granularity.md`
- `references/04_failure_taxonomy.md`
- `references/07_operational_lessons.md`

If editing a repo or world whose style is unknown to you, use the local style map from `lean4game-pattern-miner`. If you established the style yourself, you already have that context.

## Step 1: classify the level

Choose exactly one primary type:

- `first-contact`
- `definition-in-action`
- `proof-move drill`
- `notation warning`
- `retrieval`
- `transfer`
- `contrast / misconception`
- `mini-integration`
- `boss`

You may have secondary effects, but the primary type must be clear.

## Step 2: set the novelty budget

Track whether the level introduces:
- new mathematics
- new proof move
- new Lean move
- new notation

The learner has completed NNG4, so basic tactics (`rw`, `exact`,
`apply`, `intro`, etc.) and tactic-mode interaction are baseline —
never count these as new. Novelty is relative to what the course
itself has taught so far, on top of that baseline.

Each level should introduce at most one truly new burden. Everything
else should be familiar enough to be automatic, so the learner's
attention goes entirely to the new thing. This does not relax as the
course progresses.

If the theorem is mathematically deep but the Lean move is also new, cut the level or simplify the math.

## Step 3: state the dominant lesson

Write one sentence:

> This level teaches the learner to ...

Examples:
- unfold a definition of convergence with `change`
- extract a witness from an existential hypothesis
- choose a witness for an existential goal
- recognize when contradiction is the natural proof shape
- define a subsequence locally using `let` and `fun`
- avoid a notation pitfall around absolute values

If this sentence is fuzzy, the level is not ready.

## Step 4: choose the statement shape

Choose a statement whose surface mathematics makes the dominant lesson visible.

Good principle:
- hold everything else constant so the new move is easy to see.

Bad principle:
- choose the “most impressive theorem” and hope the move teaches itself.

Special rule for first-contact definitions:
- pick the simplest theorem whose proof exercises the **structure** of the definition,
- while keeping the surrounding mathematics easy enough that the learner can focus on the definition’s quantifiers, witnesses, and proof flow.

That is why a first limit-definition level is better as a constant-sequence proof than as a flashy theorem with uncontrolled side burdens.

## Step 4b: verify the statement is unexploitable

After choosing the statement, check whether it can be solved without
engaging with the dominant lesson:

- If the return type is an inhabited type (`Subgroup G`, `Nat`, etc.),
  the learner can bypass construction with `exact ⊥` or similar.
  Fix: wrap in `∃ H, H.carrier = {g | P g}` to pin the carrier.
- If the statement matches a Mathlib lemma exactly, disable that lemma
  with `DisabledTheorem` for the level.
- If available automation (`simp`, `decide`, `group`) closes the goal,
  disable the tactic for the level with `DisabledTactic`.

**Rule**: the type system or inventory must force the intended proof
shape. Hints that ask the learner to do it a certain way are not
sufficient — the learner must be *unable* to pass without doing what
the lesson teaches.

## Step 5: write the descriptive text

The level intro/docstring should do whichever is most useful:

- motivate the move,
- explain the theorem family,
- show the intended proof shape,
- name a common trap,
- or reduce notation shock.

Keep it long when necessary, but every paragraph must earn its keep.

## Step 6: decide inventory behavior

For each new item:
- visible or hidden?
- does it need a doc entry?
- should a theorem tab change?
- is this the right time to unlock it?

House standard for docs:
- what it does
- exact syntax
- when to use it
- one example
- one common misuse or warning

Do not accept weak docs for core items.

**Critical**: Use only ONE `NewTheorem`, `NewTactic`, or `NewDefinition`
command per type per level. The GameServer replaces (not appends) the
item list on each call, so a second `NewTheorem` silently overwrites the
first. To introduce multiple theorems, use a single command with multiple
arguments: `NewTheorem foo bar baz`. Different types (e.g., `NewTactic`
and `NewTheorem`) on separate lines are fine.

## Step 7: write the sample proof for pedagogy, not just correctness

The sample proof should be chosen to:
- expose the intended proof shape,
- support repertoire analysis,
- and create the right hint trigger points.

It is not enough that it compiles.

**Interactive proving principle**: lean4game is an interactive prover.
The learner types one tactic, submits it, sees the goal state change,
decides what to do next, and repeats. This try-observe-decide cycle is
how learning happens — the learner builds understanding by watching how
each move transforms the proof state. The ideal proof is a sequence of
many discrete steps, where each step participates in this cycle: the
learner can type and submit it independently, and the goal panel shows
a meaningful change that informs the next decision.

A step is bad when it breaks this cycle — when the learner must compose
a complex expression (structure literals, nested angle brackets, long
argument lists) and get it entirely right before anything happens. In
those cases there is no way to explore incrementally; the learner
either gets the whole thing right or gets nothing useful back.

This means:
- **Never use elaborate one-liners** like
  `refine ⟨{ carrier := ..., mul_mem' := ?_, ... }, rfl⟩`. The learner
  must type the entire expression correctly before anything happens.
  There is no intermediate feedback, no way to explore iteratively.
- **Prefer `apply` over `refine` for structure construction**. If a
  helper lemma or theorem can flatten a nested construction into
  `apply helper_name` followed by focused subgoals, use it. Each
  subgoal becomes a short, independent proof.
- **Use `show` to unfold opaque goals** so the learner can see what
  they're actually proving, even if Lean doesn't strictly require it.
- **Use `·` focusing** to make each obligation a clear, bounded task.
- **Avoid bundling multiple logical steps** into one tactic call. If
  `rw [a, b, c, d]` can be split into `rw [a]` then `rw [b]` etc.
  without confusion, prefer the split version for early levels.

The proof should be discoverable: a learner who tries things, reads
error messages, and backtracks should be able to make progress without
ever needing to type more than a short line at a time.

## Step 8: design hints

Use hints in layers:

### layer 1
state-reading or strategy hint

### layer 2
tool reminder or route hint

### layer 3
direct rescue hint, usually hidden

Use `Branch` whenever common wrong turns deserve dedicated rescue coverage.

Remember:
- hints are context-aware, not history-aware;
- they must be placed at the states players will actually reach.

## Step 9: decide whether to use `Template` / `Hole`

Use templates only if the main lesson is proof structure and the editor is part of the lesson.
Avoid templates when they would suppress genuine next-move choice.

## Step 10: write the conclusion

A conclusion should do at least one of:
- summarize the reusable recipe,
- translate the proof to plain mathematical language,
- explain what was subtle,
- or preview where the move returns.

A conclusion that only says “done” is weak.

## Step 11: run the two-learner test

Imagine:
- an attentive novice
- a somewhat experienced Lean user

Ask:
- Will the novice know what the level is trying to teach?
- Will the novice’s main likely failure states be recoverable?
- Will the experienced user be unnecessarily irritated by missing aliases or clutter?
- Does the level still feel coherent to both?

## Output format

Return:

1. **Dominant lesson**
2. **Primary type**
3. **Novelty budget**
4. **Statement rationale**
5. **Docstring / intro rationale**
6. **Inventory behavior**
7. **Hint plan**
8. **Conclusion rationale**
9. **Likely failure states**
10. **Full code** if code was requested

If writing Lean code, write the complete level file. No placeholders, no TODOs, no “fill this in later.”
