# W1: SetsAndMembership — Enrichment Review v2

**Reviewer**: enrichment-reviewer
**Date**: 2026-03-18
**World**: W1 SetsAndMembership (14 levels: L01–L14)
**Previous review**: v1 (7 suggestions — all appear addressed)
**Verdict**: PASS — 0 high-impact opportunities, 3 low/medium-impact suggestions

---

## v1 Status

All 7 suggestions from v1 have been addressed:

1. `.mp`/`.mpr` practice level: L10 (UsingIffHypotheses) isolates this skill.
2. `omega` formal introduction: L01 now has `TacticDoc omega` and `NewTactic omega`.
3. `Set.univ` practice level: L08 (UniversalSet) proves `A ⊆ Set.univ`.
4. ⊆/⊂ confusion warning: L03 intro includes the warning about strict subset.
5. Concrete subset level: L04 (ConcreteSubset) proves `{x | x > 5} ⊆ {x | x > 3}`.
6. Mathematical prose in first ext conclusion: L11 conclusion now includes the English translation of the proof.
7. Boss redesign: L14 (Boss) now proves antisymmetry from scratch using `ext`, with `Set.Subset.antisymm` and all aliases disabled. This is differentiated from L13 (DoubleInclusion) because L13 uses `apply Set.Subset.antisymm` while L14 must build the proof from `ext` with that theorem disabled.

---

## Ranked Suggestions

### 1. L05 `specialize` docstring has a minor pedagogical gap: it does not mention that `specialize` is destructive

**What**: The `TacticDoc specialize` says "replaces the hypothesis with the resulting statement" but does not warn that the original universal hypothesis is permanently lost after `specialize`. A learner who later has two elements to specialize the same hypothesis on (e.g., in L06's transitivity proof) could be surprised when the hypothesis is gone after the first specialization.

**Why**: L06 uses `have hxB := h1 hx` instead of `specialize h1 hx` — and does so without explaining why. The hint says "Try `have hxB := h1 hx`" but does not explain why `specialize` is not used here. A learner might try `specialize h1 hx` and succeed, but then wonder why the level used `have` instead. More importantly, the conclusion of L05 already mentions `exact h hx` as an alternative to `specialize`, but never warns that `specialize` consumes the hypothesis. Adding one sentence to L05's conclusion — "Note: `specialize` replaces the hypothesis in place, so the original universal form is lost. If you need the hypothesis again for a different element, use `have` to extract a copy instead." — would preempt confusion in L06.

**Where**: L05 conclusion or `TacticDoc specialize`

**Effort**: Low (add 1–2 sentences)

**Recommend**: Consider

---

### 2. L09 (IfAndOnlyIf) is purely mechanical — each direction is supplied as a hypothesis

**What**: L09 asks the learner to prove `P ↔ Q` given `hpq : P → Q` and `hqp : Q → P`. Both directions are already hypotheses, so after `constructor`, each subgoal is closed by `exact hpq` / `exact hqp`. The learner presses `constructor` once, then `exact` twice. There is no reasoning, no chase, no work — just assembly.

**Why**: The level's dominant lesson is "use `constructor` to split an iff." That lesson lands. But the level has zero logical content: the learner never builds an implication, never does `intro`, never reasons about why a direction holds. This means the first time the learner actually has to *prove* a direction of an iff (rather than just supplying a pre-made hypothesis) is L11 (SetExtensionality), where they must also handle `ext` and set membership simultaneously. A slightly richer L09 — e.g., `(P ∧ Q) ↔ (Q ∧ P)` where each direction requires `intro ⟨hp, hq⟩; exact ⟨hq, hp⟩` — would make the iff splitting lesson less trivial while staying within known tactics (conjunction destructuring is used in L12 anyway).

However, this is a minor concern. The current design follows a deliberate scaffold fade: L09 isolates `constructor` on iff with minimal cognitive load, L11 adds the ext context, L12 adds real chase work. The sequence is valid. The risk is that L09 teaches "iff = type two exact commands" rather than "iff = prove two implications," but L11 corrects this immediately.

**Where**: L09 statement

**Effort**: Medium (modify level statement and hints)

**Recommend**: Consider

---

### 3. The world conclusion (L14) could foreshadow W2 more concretely

**What**: L14's conclusion says "Next world: **Set Operations** — where you will learn to prove identities involving union, intersection, difference, and complement." This is informative but could be slightly more engaging by connecting to what the learner just learned. For example: "The `ext → constructor → chase` pattern you mastered here will be your main tool in the next world. The chase steps will get harder — instead of simple hypothesis application, you will need to take apart unions and intersections, handle disjunctions, and push through negations."

**Why**: Reference 00 says good conclusions "connect the level to the wider theorem family." The current conclusion connects to W2 by naming it, but does not connect the *skills* from W1 to W2. A 1–2 sentence addition that says "the pattern stays the same, but the chase gets richer" would activate the transfer layer and reduce the feeling of starting over when W2 begins.

**Where**: L14 conclusion

**Effort**: Low (add 1–2 sentences)

**Recommend**: Consider

---

## Overall Impression

**What works well**: The world is in strong shape. The 14-level structure addresses all v1 feedback: `.mp`/`.mpr` is now isolated in L10 before being used in L13, `omega` is formally documented, `Set.univ` gets its own practice level, the ⊆/⊂ warning is present, a concrete subset level exists, the first ext conclusion has mathematical prose, and the boss is meaningfully differentiated from L13. The scaffold fade from L01 (heavy guidance) through L14 (minimal hand-holding) is clean. Hint layering is consistent: strategy first, code second. The intros explain *why* the next result matters, not just what it is. The conclusions compress proofs into reusable recipes. The `ext → constructor → chase` pattern is well-named and reinforced across L11, L12, and L14.

**Single most important improvement**: None of the remaining suggestions rise to the level of "must fix." The world is pedagogically sound, has good coverage closure, appropriate scaffold fade, and a boss that integrates the world's three main skills. The three suggestions above are all "consider" — implementing any of them would make marginal improvements but their absence does not create a coverage gap or granularity defect.
