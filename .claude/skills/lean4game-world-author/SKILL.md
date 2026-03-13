---
name: lean4game-world-author
description: Use this when the user wants to design or write a full world in a lean4game course. This skill chooses the world’s granularity, level sequence, inventory release, intro/conclusion style, boss structure, and transfer logic so the world functions as a coherent chapter rather than a bag of levels.
---

# lean4game-world-author

A world is a chapter with a center of gravity.

Read:
- `references/01_patterns_from_existing_games.md`
- `references/02_technical_levers.md`
- `references/05_coverage_and_granularity.md`
- `references/03_quality_rubric.md`
- `references/07_operational_lessons.md`

If editing a repo whose style is unknown to you, first obtain the output of `lean4game-pattern-miner`. If you established the style yourself, you already have that context.

## Step 1: name the world’s promise

Write one sentence that begins:

> By the end of this world, the learner will be able to ...

If you cannot finish that sentence crisply, the world is not scoped yet.

## Step 2: choose the world type

Choose one of:
- onboarding/tutorial
- lecture
- pset
- review / consolidation

This choice changes everything:
- intro length,
- level density,
- hint density,
- whether new items are allowed,
- and boss expectations.

For proof-heavy mathematical courses, a lecture/pset alternation is a strong default:
- lecture worlds introduce and model,
- pset worlds re-cover at lower scaffolding and new surface forms.

## Step 3: set the world’s granularity

A world should usually have one dominant center:
- one theorem family,
- one proof-shape family,
- or one local conceptual block.

Do not mix several unrelated centers unless the world is explicitly a review/integration world.

**No level count limits.** A world should contain as many levels as the
learner needs to master its topic — including thorough practice, coached
retrieval, and fresh surface transfer. There is no target size and no
maximum. Never trim levels to hit a number. The only valid split triggers
are semantic: unrelated theorem families, incoherent world intro, or
cognitive overload from too many new burdens at once.

**Cognitive load principle**: Always err on the side of splitting a world
rather than risking overload. If there is even a seeming risk that a world
packs too much — split it. The cost of splitting is a little more practice
for the learner. The benefit is turning something potentially artificially
hard to understand into something manageable. Managing cognitive load is
extremely important. Watch for topics being crammed in as an "appendix"
or afterthought — if a topic has its own center of gravity (distinct
definitions, distinct proof patterns, enough content for several levels),
it should be its own world rather than squeezed into the margins of
another.

## Step 4: design the level ladder

For each level, label it as one of:
- `intro`
- `worked-example`
- `coached-practice`
- `retrieval`
- `transfer`
- `warning`
- `boss`

For every level specify:
- dominant lesson,
- new burdens,
- prior burdens being reused,
- inventory changes,
- hint philosophy,
- and what should be said in the conclusion.

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

## Step 4b: verify no level statement is exploitable

For each level in the ladder, check that the statement type forces the
intended proof. Common exploits to watch for:

- **Unconstrained return type**: `Subgroup G`, `Nat`, or any inhabited
  type can be solved with `exact ⊥` / `exact 0` / etc. Fix: wrap in
  `∃ H, H.carrier = {g | P g}` or similar to pin the construction.
- **Library one-shot**: If the statement matches a Mathlib lemma,
  `exact that_lemma` bypasses the level. Fix: `DisabledTheorem` for
  that level.
- **Automation one-shot**: If `simp`/`decide`/`group` closes the goal
  and those tactics are available, the level teaches nothing. Fix:
  `DisabledTactic` for that level.

**Rule**: hints that ask the learner to use a specific approach are not
sufficient. The type system or inventory must make the bypass impossible.

## Step 4c: verify proofs are interactive

For each level in the ladder, check that the intended proof consists
of many short, discrete tactic steps (~12 characters each). Each step
should change the goal state visibly so the learner gets immediate
feedback.

Red flags:
- **Elaborate one-liners**: `refine ⟨{ field := ..., ... }, rfl⟩` or
  any multi-line expression the learner must type entirely before
  anything happens. Replace with `apply` + focused subgoals.
- **Opaque goals**: After `apply` or `intro`, the goal shows
  set-membership notation like `x ∈ {g | P g}` instead of the
  concrete predicate. Add `show` steps to unfold.
- **Bundled rewrites**: `rw [a, b, c, d, e]` where each step could
  be done separately. In early levels, prefer separate steps.

The learner will play around, try tactics, see what happens, and
backtrack. The proof design must support this exploration. Helper
lemmas (like `Subgroup.mk_carrier`) that convert complex constructions
into `apply` + focused obligations are strongly preferred over asking
the learner to write structure literals.

## Step 5: plan coverage closure

List the world’s core items and show how each gets:
- introduction,
- supported use,
- retrieval,
- and boss integration.

If a core item skips straight from introduction to boss, the world is underprepared.

## Step 6: plan the world intro

A world intro should do at least one of:
- motivate the coming theorem family,
- tell a historical or conceptual story,
- preview the proof shape,
- or warn about the main trap.

Lecture intros may be long if they do real conceptual work.  
Pset intros should be shorter and more challenge-oriented.

## Step 7: plan inventory behavior

For each new item:
- visible or hidden?
- doc entry required?
- theorem tab?
- why now?

Use:
- `NewHiddenTactic` for harmless alias support,
- `Only*` / `Disabled*` to focus attention,
- and named statements only when later reuse is intended.

## Step 8: design the boss

A boss should:
- require several moves seeded earlier,
- expose weak coverage,
- and produce a real “now I see the whole method” moment.

Write down the boss’s dependency chain explicitly:
- which earlier levels seeded which subskills.

If the boss depends on an unseeded move, redesign the world.

## Step 9: decide what files need to exist

If writing code, produce complete files as needed:
- world file
- level files
- doc files if new docs are added
- `Game.lean` edits if imports or dependencies must change

Never produce stubs.

## Output format

Return:

1. **World promise**
2. **World type and rationale**
3. **Coverage closure table**
4. **Level ladder**
5. **World intro draft**
6. **Inventory plan**
7. **Boss design**
8. **Files to create or edit**
9. **Risks and likely learner failure points**
10. **Playtest focus**

If asked for code, append the full code after the design section.
