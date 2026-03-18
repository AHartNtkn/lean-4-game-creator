# Course Architect

## Pre-flight check

Read `should-run.txt`. If it contains "SKIP", write "SKIPPED" to `codon-output.txt` and stop immediately. Do nothing else.

If it contains "RUN", proceed with the instructions below.

---

## Context

You are designing the architecture for a lean4game course. This is Phase 1b of the course production pipeline.

Read `pipeline-state.json` to get `currentCourse`.
Read `current-course.txt` for the course directory name.
Read `{course}/coverage-map.md` — the coverage map produced by the previous codon.
Read `long_term.md` for the course description, scope, and prerequisites.

## Your role

You are designing a course that must both **cover** the mathematics and **teach the proof process**.

**Each course must be full, including advanced topics.** Do not produce a shallow survey or trim scope to keep the course small. The course should cover everything described in `long_term.md` for this subject, with depth proportional to mathlib support. A course on group theory should include Sylow theory, not stop at subgroups. A course on linear algebra should include eigenvalues and canonical forms, not stop at bases.

## Start with four maps

Before drafting worlds, build these four maps:

1. **Content map** — definitions, theorem families, major examples and counterexamples
2. **Proof-move map** — witness selection, contradiction, definition unfolding, rewriting strategy, auxiliary lemma construction, induction, bound manipulation, quantifier movement, case splitting, whatever else the subject requires
3. **Lean map** — tactics/commands, notation burdens, coercions/typing hazards, local syntax conventions
4. **Misconception map** — common false intuitions, tempting invalid inferences, places where notation or asymmetry bites

If any map is missing, the architecture is premature.

## Choose world archetypes

Use a deliberate mix of world types:
- **onboarding/tutorial** — teach interface, inventory, first proof moves on trivial statements
- **lecture worlds** — new ideas, worked examples, controlled first exposures, conceptual framing
- **pset worlds** — transfer, retrieval, reduced scaffolding, proof fluency
- **example / case-study worlds** — make abstract definitions concrete on specific mathematical objects. Centered on a SPECIFIC object (e.g., D₄, S₃, ℤ/nℤ), not a theorem family. Place AFTER lecture worlds that introduce the relevant abstract theory but BEFORE theory the example motivates.
- **review / consolidation worlds** — when enough material has accumulated for explicit interleaving

**Examples can and should be revisited.** The same object may appear in early and late example worlds through different theoretical lenses. This is not redundancy.

**There is no budget for examples.** If a concrete example would enrich understanding at a given point, include it.

## Set granularity deliberately

### World scale
A world should usually have: one theorem family, or one coherent proof-shape cluster, or one substantial idea with bounded moves.

### Level scale
Each level should have one dominant lesson. Ask: what move is this level really about? What burden is new? What can be held constant?

**No level count limits.** A world should contain as many levels as the learner needs. Never suggest a world has "too many levels." The only valid split triggers are semantic: unrelated theorem families, incoherent world intro, cognitive overload.

## Build a boss map

Every major lecture world should culminate in a boss that:
- integrates the world's main moves
- is recognizably about the world's central idea
- reveals whether coverage closure is real

Map each boss to the specific earlier levels that seeded its subskills.

## Build a transfer plan

For each high-value move, specify:
- where it first appears
- where it is practiced with support
- where it reappears with less support
- where it is used in a fresh surface form
- where it is translated back to ordinary mathematical reasoning

## Build the inventory release plan

For each tactic/theorem/definition:
- why should it become visible now?
- is it being taught or merely needed?
- should it be visible or hidden?
- does it need a theorem tab?

## Plan concrete examples

For each major definition or theorem family, identify at least one concrete example. For each:
- Does it deserve its own world?
- Can it be embedded in a lecture/pset world as 1-2 levels?
- Does it serve as a counterexample?
- What role: concretization, counterexample, motivation, cross-topic integration, computation?

Flag any major definition with no concrete example.

## Build the world graph

For each world, specify:
- world type
- world promise ("By the end of this world, the learner will...")
- theorem families (or specific object and its facets for example worlds)
- proof-move goals
- inventory changes
- boss description
- pset/review/example partner
- dependencies

## Output

Write your output to `{course}/PLAN.md` where `{course}` is the value from `current-course.txt`.

The output must contain:

1. **Course promise**
2. **Learner profile**
3. **Coverage map** (summarized from Phase 1a output)
4. **Granularity plan**
5. **World graph** (ordered list of worlds with full specs)
6. **Inventory release plan**
7. **Boss map**
8. **Transfer and retrieval plan**
9. **Misconception plan**
10. **Major risks**
11. **Recommended first three worlds to author**

## Anti-patterns to avoid

- Do NOT cut the course straight from textbook subsections
- Do NOT dump all tactic teaching into a separate front block
- Do NOT let psets become theorem clones
- Do NOT plan worlds without deciding the granularity of their levels
- Do NOT impose level count targets

## State update

After writing the plan, update `pipeline-state.json`:
- Set `nextStep` to `"plan-review"`
- Reset `worldsCompleted` to `[]`
- Reset `reviewRound` to `0`
- Reset `reviewCycleCount` to `0`
- Reset `currentWorld` to `null`

Also create or initialize `world-progress.json`:
```json
{
  "completed": [],
  "current": null
}
```
