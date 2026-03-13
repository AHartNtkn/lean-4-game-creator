# Patterns from existing games

This file distills design patterns from **NNG4** and **RealAnalysisGame** that are worth copying on purpose.

## 1. NNG4: tactic-first onboarding with a clear boss

The tutorial world in NNG4 is tiny, explicit, and honest about its goal.

Patterns worth copying:

- The world introduction tells the learner the boss theorem up front.
- Early levels isolate one tactic at a time.
- The first level’s conclusion points the learner back to the inventory.
- The final tutorial level gives an example proof after success.
- The game teaches proof *moves* using mathematically simple statements.

Interpretation:

NNG4 is not pretending that the theorem `2 + 2 = 4` is the mathematical point. The point is that the learner can now read a goal state and execute a short, coherent tactic sequence. The arithmetic is chosen to make the proof move visible.

## 2. RealAnalysisGame: coverage by syllabus, granularity by proof move

RealAnalysisGame tracks a real course syllabus, but its level granularity is not “one textbook theorem per level.” Its granularity is finer and more useful.

A likely way to understand its design is:

- **coverage** comes from the real-analysis syllabus,
- **granularity** comes from the proof moves and Lean moves needed to formalize that syllabus.

That is why:

- Lecture 1 spends a whole world on historical motivation plus basic tactics.
- Lecture 2 introduces the definition of sequence convergence through the constant-sequence theorem, where the mathematics is trivial and the real lesson is the epsilon–N proof shape.
- Later worlds separate algebraic limit operations before asking for a product big boss.
- Psets revisit the same moves on new surfaces, rather than merely listing new theorems.

This is the core lesson: **choose what to cover from the mathematics; choose how finely to cut it from the proof process.**

## 3. RealAnalysisGame uses alternating world archetypes

The game alternates between different world types:

- **lecture worlds**: long intros, conceptual framing, explicit strategy talk, new definitions/theorems/tactics
- **pset worlds**: shorter intros, more transfer, fewer explanations, practice under reduced scaffolding
- **boss levels** inside lecture worlds: integration of a world’s repertoire

This creates a healthy rhythm:
- explanation,
- coached use,
- transfer,
- integration,
- then back to new material.

## 4. RealAnalysisGame uses narrative to motivate rigor

The real-analysis course is not just a theorem list. The world intros use historical narrative, conflict, pictures, and conceptual stakes.

What this seems to be doing pedagogically:
- giving a reason to care before formalization,
- turning definitions into answers to real problems,
- and lowering the sense that proof is arbitrary bureaucracy.

The narrative is not decorative. It is curriculum.

## 5. RealAnalysisGame keeps teaching strategy even in advanced worlds

The advanced lecture levels still explain:
- why this theorem matters,
- what the key trick is,
- what proof shape to try,
- and what common mistake to avoid.

This is important. Many technical courses stop explaining once the material gets hard. RealAnalysisGame does not.

The lesson is:
**as mathematical sophistication rises, strategy explanation matters more, not less.**

## 6. RealAnalysisGame repeatedly translates Lean into ordinary mathematical language

Some levels end by restating the formal proof in plain English.

This supports:
- proof comprehension,
- paper-proof transfer,
- and the learner’s sense that the Lean proof was not just syntax manipulation.

## 7. Psets are not merely “more of the same”

A pset level may:
- give a fresh surface form,
- remove hints,
- add a mild twist,
- or introduce a lightweight proof-structuring move when the math burden is controlled.

The right rule is not “psets never teach.”  
The right rule is “psets should not carry the main burden of first explanation for high-load ideas.”

## 8. Coverage and granularity in the real-analysis example

A useful reconstruction of the design logic is:

### Macro coverage
Follow the actual course:
- limits of sequences,
- algebraic limit theorems,
- Cauchy sequences,
- subsequences,
- construction/completion,
- series,
- continuity,
- derivatives,
- uniform convergence,
- integration,
- compactness,
- cardinality / IVT.

### Meso coverage
Break each chapter into theorem families:
- constant limits,
- sum limits,
- product limits,
- order limits,
- subsequence results,
- Cauchy machinery, and so on.

### Micro granularity
For each family, isolate the local proof moves:
- unfold `SeqLim`,
- introduce epsilon and positivity hypotheses,
- choose a witness,
- specialize universal hypotheses,
- use boundedness to control a product term,
- use contradiction to transfer order to limits,
- define a subsequence with `let` and `fun`,
- split conjunctions/disjunctions,
- build auxiliary facts with `have`,
- handle coercions and algebraic normalization.

The striking point is that the game is organized much more by this micro layer than a textbook would be.

## 9. Practical pattern to imitate

When planning a new course, ask:

1. What does the mathematical syllabus require by the end?
2. What proof families realize that syllabus?
3. What micro-moves are required for each proof family?
4. Which of those micro-moves deserve their own levels?
5. Which clusters of levels form a coherent world?
6. Which world deserves a boss?
7. Where should transfer happen under reduced scaffolding?

If the answer starts from theorem statements alone, the course will usually be too coarse.

## 10. Neither reference game models example worlds well

NNG4 uses natural numbers as a substrate — the arithmetic is always the vehicle,
never the destination. RealAnalysisGame follows an analysis syllabus and does
not dedicate worlds to exploring specific sequences, specific functions, or
specific metric spaces as concrete objects.

This is a gap in the reference material, not a pattern to imitate. A good
course in most mathematical subjects needs worlds where the learner works with
a **specific object** — computing its properties, verifying definitions against
it, and seeing counterexamples that break conditions. In group theory, this
means worlds centered on D₄, S₃, ℤ/nℤ, the Klein four-group, etc. In
analysis, it would mean worlds centered on specific sequences or functions.

These example worlds serve purposes that no other archetype covers:
concretization of abstract definitions, counterexample generation, intuition
building, cross-topic integration on a single familiar object, and computation
training. A course that only has lecture, pset, and review worlds produces
learners with abstract fluency but no concrete intuition.

Example worlds can and should revisit the same object as new theory becomes
available. There is no budget for them — if a concrete example would enrich
the learner at a given point, it should be included.
