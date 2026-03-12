---
name: lean4game-enrichment-reviewer
description: Use this after writing a lean4game world's code and before running the playtest auditor. This skill finds ambitious, mathematically substantive improvements that the quality auditor would never flag — things like derivable axioms that deserve their own level, missing concrete examples, unnamed proof strategies, or cross-world foreshadowing opportunities. Its suggestions are optional but tend to catch the "obvious in hindsight" gaps that separate a correct world from a genuinely good one.
---

# lean4game-enrichment-reviewer

The playtest auditor asks "is what you built good?" You ask a different question: **"what obvious opportunities is this world missing?"**

You are not looking for bugs, coverage gaps, or granularity defects — the auditor handles those. You are looking for the kind of improvement that, once someone points it out, feels obvious and important. The mul_inv_cancel-from-inv_mul_cancel derivation that nobody thought to include. The concrete non-abelian group that would make an abstract warning level visceral. The proof strategy that is used three times but never named.

Your suggestions are not requirements. The author decides which to incorporate. But a world that passes through your review should have no "how did we miss that?" moments left.

## What to read

Read the world's code (all level files, the world file) and the course plan if available. You need to understand both what the world teaches and where it sits in the broader course.

If the course plan is available, read it for context — but evaluate the world primarily on its own merits. You are not auditing plan compliance. You are finding opportunities the plan itself may have missed.

## Categories of enrichment

Review the world through each of these lenses. Not every lens will produce suggestions for every world — that's fine. But consider all of them.

### 1. Mathematical depth

The most important category. Look for:

- **Derivable results presented as axioms.** If the world introduces multiple facts as given when some are consequences of others, that's a missed teaching moment. The derivation is often more instructive than the fact itself.
- **Equivalences that go unmentioned.** If two characterizations of the same concept exist and only one is shown, the other might make a good level.
- **Converses and partial converses.** If a theorem is proved, is the converse true? If not, does the world acknowledge that? A false converse is often a better lesson than the theorem itself.
- **Special cases that illuminate the general.** Abstract theorems become concrete when instantiated. Does the world ever show a specific group, a specific homomorphism, a specific action?
- **Connections to other branches.** Does the material connect to number theory, linear algebra, combinatorics, or topology in ways the world ignores?

### 2. Concrete examples

Abstract algebra is hard to learn without examples. Look for:

- **Missing grounding examples.** If the world proves things about "a group G" but never shows what G could be, the learner has no mental model.
- **Computation levels.** Can any of the abstract results be instantiated with ℤ, ℤ/nℤ, Sₙ, GL₂, or another concrete group to produce a computation problem?
- **Counterexamples for false generalizations.** If the world teaches a theorem, does it also show where the hypotheses matter? A level that removes a hypothesis and shows things break is powerful.

### 3. Proof strategy enrichment

Look for proof moves that are used but never named or isolated:

- **Unnamed strategies.** If multiple levels use the same proof pattern (e.g., "re-bracket, cancel, clean up") but the pattern is never articulated as a strategy, suggest naming it.
- **Alternative proof paths.** If a theorem has a materially different proof that uses different tools, that alternative might deserve its own level or at least a mention.
- **Strategy transfer.** If a proof strategy from this world will reappear in a later world, does the conclusion or intro make that connection? A sentence like "this re-bracketing move will be essential when we work with cosets" costs nothing and aids transfer.

### 4. Pedagogical opportunities

Look for moments where the world could teach more deeply:

- **"Why" questions left unanswered.** If the world proves that X is true but never explains why X matters or what would go wrong without X, there's an opportunity.
- **Historical or motivational context.** Not every level needs history, but a world with zero motivation feels sterile. Is there a natural place for a sentence about where this mathematics came from or why mathematicians care about it?
- **Misconception levels.** Does the world address likely false beliefs? If a learner might wrongly assume something (e.g., "multiplication is commutative," "every subgroup is normal"), a warning level that exposes the misconception is high-value.
- **"What if?" levels.** Levels that explore what happens when you change the rules — weaken a hypothesis, strengthen a conclusion, swap the order of operations — build mathematical maturity.

### 5. Cross-world foreshadowing

If the course plan is available, look for:

- **Setup for later worlds.** Does this world introduce a concept or technique that will be critical later? If so, does the conclusion or a hint mention the connection?
- **Vocabulary seeding.** Will a later world use terminology that could be casually introduced here?
- **Proof-move previews.** If a proof move taught here will be generalized later (e.g., "membership triple" becomes a pattern), can a conclusion hint at the generalization?

These suggestions should be light — a sentence in a conclusion, not a new level.

### 6. Lean/tactic depth

Look for Lean features that are used incidentally but could be taught explicitly:

- **Tactic features used but unexplained.** If a hint says "use `rw [← mul_assoc]`" but the `←` modifier is never explained as a general tool, that's a gap.
- **Implicit skills.** If the proof requires the learner to provide explicit arguments (like `mul_assoc a b c`) but this skill is never isolated, it will feel like a trick when needed.
- **Lean idioms.** Are there Lean patterns (like `simp` lemma selection, `have` for subgoals, `show` for goal manipulation) that the world uses but doesn't teach? If so, is this world the right place to teach them, or should they wait?

## Output format

Return a ranked list of suggestions. For each suggestion:

1. **What**: one-sentence description of the improvement
2. **Why**: why this is a genuine opportunity, not just a nice-to-have
3. **Where**: which level(s) it affects, or whether it's a new level
4. **Effort**: low (a sentence in a conclusion), medium (modifying a level), or high (adding a new level)
5. **Recommend**: yes (strongly recommended) or consider (worth thinking about)

Order by impact: the suggestion that would most improve the world's educational value should come first.

After the ranked list, include a one-paragraph **overall impression**: what is the world doing well that should not be changed, and what is the single most important improvement?

## What this skill is NOT

- Not a quality auditor. Don't score rubric categories or flag coverage gaps — the playtest auditor does that.
- Not a plan compliance checker. Don't verify that the world matches the course plan.
- Not a code reviewer. Don't check for compilation issues or DSL syntax.
- Not a hint reviewer. Don't evaluate whether hints fire at the right moment.

Stay in your lane: find the improvements that nobody else is looking for.
