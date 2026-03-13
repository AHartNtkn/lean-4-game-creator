---
name: lean4game-course-architect
description: Use this when the user wants to design a new lean4game course, redesign an existing one, or decide what to cover and in what order. This skill turns a topic or syllabus into a world graph, coverage plan, granularity plan, inventory release plan, boss map, and playtesting agenda.
---

# lean4game-course-architect

You are designing a course that must both **cover** the mathematics and **teach the proof process**.

Read:
- `references/00_what_good_looks_like.md`
- `references/01_patterns_from_existing_games.md`
- `references/05_coverage_and_granularity.md`
- `references/02_technical_levers.md`
- `references/07_operational_lessons.md`

## Start with four maps

Before drafting worlds, build these four maps:

1. **Content map**
   - definitions
   - theorem families
   - major examples and counterexamples

2. **Proof-move map**
   - witness selection
   - contradiction
   - definition unfolding
   - rewriting strategy
   - auxiliary lemma construction
   - induction
   - bound manipulation
   - quantifier movement
   - case splitting
   - subsequence construction
   - whatever else the subject requires

3. **Lean map**
   - tactics / commands
   - notation burdens
   - coercions / typing hazards
   - local syntax conventions

4. **Misconception map**
   - common false intuitions
   - tempting invalid inferences
   - places where notation or asymmetry bites

If any map is missing, the architecture is premature.

## Choose world archetypes

Use a deliberate mix of world types. The default strong mix is:

- **onboarding/tutorial**
- **lecture worlds**
- **pset worlds**
- **review or consolidation worlds** when needed

### Onboarding/tutorial
Use this to teach how to read the interface, use the inventory, and execute the first proof moves on mathematically trivial statements.

### Lecture worlds
Use these for:
- new ideas,
- worked examples,
- controlled first exposures,
- and conceptual framing.

### Pset worlds
Use these for:
- transfer,
- retrieval,
- reduced scaffolding,
- and proof fluency.

### Review worlds
Use these when the course has accumulated enough material that interleaving and retrieval should be made explicit rather than accidental.

## Set granularity deliberately

### World scale
A world should usually have:
- one theorem family,
- or one coherent proof-shape cluster,
- or one substantial idea with a clearly bounded set of moves.

### Level scale
Each level should have one dominant lesson.
Do not let the theorem statement decide the cut by itself.

Ask instead:
- what move is this level really about?
- what burden is new?
- what can be held constant so that burden is visible?

## Build a boss map

Every major lecture world should culminate in a boss or capstone level that:
- integrates the world’s main moves,
- is recognizably about the world’s central idea,
- and reveals whether coverage closure is real.

Map each boss to the specific earlier levels that seeded its subskills.

## Build a transfer plan

For each high-value move, specify:
- where it first appears,
- where it is practiced with support,
- where it reappears with less support,
- where it is used in a fresh surface form,
- and where it is translated back to ordinary mathematical reasoning.

A course without this plan is bluffing about mastery.

## Build the inventory release plan

For each tactic/theorem/definition:
- why should it become visible now?
- is it being taught or merely needed?
- should it be visible or hidden?
- does it need a theorem tab?
- what doc standard is required?

Treat this like release management for cognitive load.

## Build the world graph

For each world, specify:
- world type,
- world promise,
- theorem families,
- proof-move goals,
- inventory changes,
- boss,
- pset partner or review partner,
- and dependencies.

Where conceptual prerequisites are not captured by the automatic graph, plan explicit `Dependency` edges.

## Output format

Return:

1. **Course promise**
2. **Learner profile**
3. **Coverage map**
4. **Granularity plan**
5. **World graph**
6. **Inventory release plan**
7. **Boss map**
8. **Transfer and retrieval plan**
9. **Misconception plan**
10. **Major risks**
11. **Recommended first three worlds to author**

## Anti-patterns

Do not:
- cut the course straight from textbook subsections,
- dump all tactic teaching into a separate front block and never revisit it,
- let psets become theorem clones,
- plan worlds without deciding the granularity of their levels,
- or impose level count targets or split triggers based on level count.

**No level count limits.** A world exists to help the learner master its
topic. It should contain as many levels as that requires — including
thorough practice, coached retrieval, and fresh surface transfer. There
is no target size. A world with 5 levels and a world with 20 levels can
both be correctly scoped if each level belongs to the world's center of
gravity. The only valid split triggers are semantic: unrelated theorem
families, incoherent world intro, or cognitive overload from too many
new burdens at once. Never suggest "this world has too many levels" as a defect.

The architecture should make later authoring easier, not harder.
