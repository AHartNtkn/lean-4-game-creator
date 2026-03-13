---
name: lean4game-playtest-auditor
description: Use this when the user wants to know whether a lean4game level, world, or whole game is actually good. This skill red-teams the content for coverage, granularity, recoverability, proof-move teaching, boss integrity, technical fit, and maintenance risks. Compilation is only the first check.
---

# lean4game-playtest-auditor

Your job is to find the ways a draft can be **correct but bad**.

Read:
- `references/03_quality_rubric.md`
- `references/04_failure_taxonomy.md`
- `references/05_coverage_and_granularity.md`
- `references/07_operational_lessons.md`

## Audit in this order

### 1. Technical sanity
Check for:
- build or import issues
- missing docs for new visible items
- hidden alias opportunities
- broken dependencies
- world size problems
- hint placement risks

### 1b. Statement exploitability

For every level, check whether the statement type can be satisfied by
a trivial or unintended proof that bypasses the intended lesson.

Common exploit patterns:
- **Unconstrained return type**: A goal of `Subgroup G` (or any
  structure/type with known inhabitants) can be solved by `exact ⊥`,
  `exact ⊤`, `exact default`, etc. without engaging with the lesson.
  Fix: wrap in `∃ H : T, H.carrier = {g | P g}` or similar to pin
  the specific construction.
- **Overly general existential**: `∃ x, P x` where `P` is satisfied
  by a trivially known witness (e.g. `exact ⟨0, rfl⟩`).
- **Provable by automation**: If `simp`, `decide`, `omega`, or `aesop`
  closes the entire goal and those tactics are available, the level
  teaches nothing. Either disable the tactic or make the statement
  require manual steps.
- **One-shot by a library lemma**: If the statement matches a Mathlib
  theorem exactly, `exact that_lemma` closes it. Disable the theorem
  for that level using `DisabledTheorem` — the statement form itself
  is fine.

**The test**: for each level, ask "can the learner pass WITHOUT doing
what the dominant lesson teaches?" If yes, the statement must be
redesigned or the trivial proof path must be disabled. Asking nicely
via hints is not sufficient — the type system or inventory must force
the intended proof shape.

Flag any exploitable statement as a P0 (blocking) defect.

### 1c. Interactive proof quality

For every level, check that the intended proof is a sequence of
discrete tactic steps, where each step can be typed and submitted
independently and produces a visible change in the goal state. The
test: can the learner explore incrementally — type a step, see how
the proof state changed, decide what to do next? Steps that require
composing a complex expression before any feedback appears break this
cycle.

Red flags to check:
- **Elaborate one-liners**: Any tactic call that spans multiple lines
  or requires the learner to type a complex expression (structure
  literals, nested angle brackets with multiple fields) before getting
  any feedback. Flag as P1 (high).
- **No intermediate feedback**: A proof step that doesn't visibly
  change the goal state (e.g., a `refine` that just adds metavariables
  the learner can't see). Flag as P2 (medium).
- **Opaque goals**: After `apply` or `intro`, the goal displays
  set-membership like `x ∈ {g | P g}` rather than the concrete
  predicate `P x`. Missing `show` step. Flag as P2.

**The principle**: lean4game is an interactive prover. The learner types
one short tactic, sees the result, decides what to do next. Proofs that
require getting a long expression exactly right before anything happens
are hostile to exploration and discovery. Prefer `apply helper` +
focused subgoals over `refine ⟨{ ... }, ...⟩`.

### 2. Coverage sanity
Check whether:
- core items have closure,
- proof moves are actually taught,
- notation and misconceptions are covered,
- transfer exists,
- and major definitions are concretized on specific examples (not only exercised abstractly).

### 3. Granularity sanity
Check whether:
- levels are overbroad or overfine,
- the world center of gravity is stable,
- bosses are properly seeded,
- and the world provides enough practice for mastery.

**No level count limits.** Never flag a world for having "too many levels."
A world should contain as many levels as the learner needs to master its
topic — including thorough practice, coached retrieval, and fresh surface
transfer. The only valid split triggers are semantic: unrelated theorem
families, incoherent world intro, or cognitive overload from too many
new burdens at once. A world with 20 levels on a single coherent topic is fine.
A world with 6 levels that skimps on practice is a defect.

**Cognitive load principle**: If the world covers multiple unrelated theorem
families or proof-shape families, flag it for splitting. The cost of
splitting is a little more practice; the benefit is turning something
potentially artificially hard into something manageable. A world that
"could be two worlds" should be two worlds. Watch for topics that are
crammed in as an "appendix" or afterthought to another world's main
content — if a topic has its own center of gravity (distinct definitions,
distinct proof patterns, enough content for several levels), it should
not be squeezed into the margins of a different world.

### 4. Learner simulation
Simulate at least:
- an attentive novice
- a more experienced Lean user

For the novice, identify:
- first likely stuck point
- most likely wrong move
- whether hints rescue well
- whether the level’s lesson is legible

For the experienced user, identify:
- avoidable friction
- alias gaps
- inventory clutter
- needless forced verbosity

### 5. Course-role sanity
Ask whether the level or world plays its intended role:
- introduction
- practice
- transfer
- review
- boss
- pset
- lecture
- example / case-study

A transfer level that behaves like a first-contact level is miscast.
A boss that behaves like a worked example is miscast.
An example world that introduces new abstract theory instead of exercising
existing theory on concrete ground is miscast.

## Required checks for any boss

For a boss, explicitly verify:
- seeded subskills,
- closure quality,
- integration quality,
- surprise burden,
- and whether a learner could explain in words why the proof works.

## Required checks for any pset

For a pset or pset world, explicitly verify:
- fresh surface form,
- reduced scaffolding,
- real retrieval,
- and whether the problems are doing more than cloning lecture material.

## Required checks for any first-contact level

For a first-contact level, explicitly verify:
- that the mathematics is simple enough for the new move to stand out,
- that the doc entry is sufficient,
- and that there is a rescue path.

## Output format

Return:

1. **Overall verdict**
2. **Rubric scores**
3. **Coverage gaps**
4. **Granularity defects**
5. **Learner simulation notes**
6. **Boss or pset integrity notes** as relevant
7. **Technical risks**
8. **Ranked patch list**
9. **What to playtest again after patching**

Be blunt. “Compiles” is not a verdict.
