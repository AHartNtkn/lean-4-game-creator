# Enrichment Review (Round 2): W3 ListBasics

This is a second-pass review after the world was substantially re-authored in response to the first enrichment review. The first review identified ten issues; the re-authored world addressed the most critical ones. This review evaluates what remains.

## What was fixed since the first review

The re-authored world addressed the first review's highest-priority items:

1. **Nodup level added** (was #1). L09 now teaches `List.Nodup` with `List.nodup_cons` and `List.nodup_nil`, including the contrast with `[1, 2, 1]`. The plan's M17 (I) coverage is restored.

2. **Genuine proof reasoning throughout** (was #2). Every level from L02 onward disables `decide` (and most disable `simp` too). The learner must use `rw`, `left`/`right`, `exact`, `refine`, and `constructor` to navigate real proof structure. No level is solvable by pressing a single automation button.

3. **Fin-indexing level added** (was #3). L08 teaches `List.get` with `Fin l.length`, explicitly connecting back to W1. The conclusion discusses matrices, sums, and `Finset.range` as future uses.

4. **Map preserves membership** (was #6). L05 now proves `a in l -> f a in List.map f l` symbolically using `List.mem_map` and an existential witness, rather than computing on a concrete list.

5. **Filter level cleaned up** (was #7). L06 now uses `p : Nat -> Bool` directly with `p a = true`, avoiding the `fun x => decide (x < 4)` encoding and the `Prop`/`Bool` confusion.

6. **Boss exercises map and filter** (was #8). L11 proves `f a in List.filter p (List.map f l)` given `a in l` and `p (f a) = true`, composing filter membership, map membership, an existential witness, and a conjunction. This is a genuine multi-step integration.

7. **Permutation foreshadowing added** (was #4). The boss conclusion includes a "Permutations preview" paragraph seeding `List.Perm` vocabulary for W4.

8. **Transfer moment strengthened** (was #9). The boss conclusion includes a transfer paragraph connecting each tactic step to a sentence in a paper proof argument.

## Ranked suggestions

### 1. L02 proves a near-tautology -- the rewrite step is not genuinely instructive

**What**: L02 asks the learner to prove `(0 :: l).length = l.length + 1` using `rw [List.length_cons]`. After the rewrite, the goal is `l.length + 1 = l.length + 1`, which Lean closes automatically. The learner applies one rewrite and is done.

**Why**: This is the world's first level with `decide` disabled, intended to teach symbolic reasoning with API lemmas. But the proof is "rewrite, done" -- the rewrite is the entire proof, and the result after rewriting is trivially `rfl`. The learner practices the mechanical act of `rw` but does not see why rewriting is *useful* (i.e., it did not simplify something non-obvious or transform a hard goal into an easy one).

A stronger version would require a two-step rewrite. For example, proving `(0 :: 1 :: l).length = l.length + 2` would require `rw [List.length_cons, List.length_cons]` followed by `omega` (or `ring`). This teaches the same lemma but demonstrates that rewrites compose and that auxiliary cleanup (with `omega`) is sometimes needed after rewriting. The learner sees: "rewrite twice, then clean up the arithmetic" -- a more representative proof pattern.

**Where**: L02 (ListLength). Modify the statement.

**Effort**: Medium (changing the statement and hints of one level).

**Recommend**: Consider. The current level is functional, and the two-step version is already latent in L07 (ListAppendLength). But L02 is the learner's first encounter with symbolic list reasoning after L01's `rfl`, so there is value in making it more substantive.

---

### 2. L07 (AppendLength) is one-step `rw` with no arithmetic follow-up -- same issue as L02

**What**: L07 proves `(l1 ++ l2).length = l1.length + l2.length` via `rw [List.length_append]`. This is identical in structure to L02: single rewrite, immediate `rfl` close.

**Why**: This level exists to practice "rewrite with a structural lemma." But L02 already practiced exactly this pattern. Two levels with the same shape (apply one rewrite, done) is a missed opportunity. If one of L02 or L07 required composing rewriting with arithmetic, the pair would demonstrate progression rather than repetition.

For example, L07 could instead prove `(l1 ++ l2).length + (l2 ++ l1).length = 2 * (l1.length + l2.length)` which requires two applications of `List.length_append` plus `omega` or `ring`. Or it could prove `(l1 ++ [a]).length = l1.length + 1`, composing `List.length_append` with `List.length_singleton` -- showing that different API lemmas can be chained. Either version would make L07 feel like a genuine step up from L02 rather than a replay.

**Where**: L07 (AppendLength).

**Effort**: Medium (changing the statement and hints).

**Recommend**: Consider. The current version is adequate as a retrieval level, but making it non-trivially different from L02 would strengthen the world's proof-move progression.

---

### 3. The Nodup level (L09) mentions `[1, 2, 1]` failing but only in the conclusion -- the learner never *experiences* the failure

**What**: L09 proves `[1, 2, 3].Nodup` and the conclusion explains that `[1, 2, 1].Nodup` would fail. But the learner never attempts the failing case.

**Why**: Seeing a definition succeed is necessary. Seeing it *fail* is what builds genuine understanding. The first review's suggestion #1 specifically called for "Prove a specific list has no duplicates, and show one that does [have duplicates]" (quoting the plan). The plan says W3.7 should cover both sides. The current level only covers the success case; the failure case is relegated to a textual remark.

A clean way to address this without adding a whole new level: make L09 a two-part level. The first goal proves `[1, 2, 3].Nodup`. The second goal proves `1 in [2, 1]` (i.e., the learner proves the fact that *blocks* `[1, 2, 1].Nodup`). The conclusion then connects these: "You proved `1 in [2, 1]`, which means `1 :: [2, 1] = [1, 2, 1]` fails `nodup_cons` at the first step." This is low-cost and high-impact.

Alternatively, a separate companion level L09b could ask the learner to prove `not [1, 2, 1].Nodup` or to prove `1 in [2, 1]` and explain why this means `[1, 2, 1]` has duplicates.

**Where**: L09 (Nodup), or a new L09b.

**Effort**: Medium (adding a second goal to L09 or adding a level).

**Recommend**: Yes. The plan explicitly says "show one that does [have duplicates]" and the learner's understanding of `Nodup` is incomplete without seeing a failure.

---

### 4. No level practices the backward direction of a membership `iff` -- only forward directions are used

**What**: L03 uses `List.mem_cons` (forward: unfold, choose left/right). L04 uses `List.mem_append` (forward: unfold, choose left/right). L05 uses `List.mem_map` (forward: unfold, provide witness). L06 uses `List.mem_filter` (forward: unfold, split conjunction). L10 combines forward directions. L11 combines forward directions. No level ever uses a membership lemma in the *backward* direction -- starting from `a in b :: l` and extracting `a = b or a in l` via `rcases` or `obtain`.

**Why**: This is a proof-move gap. The forward direction ("I know the components, assemble the membership") is one skill. The backward direction ("I have membership, destructure it to learn something") is a different and equally important skill. Specifically, `rcases h : a in b :: l with rfl | hmem` (case-splitting on how `a` got into the list) is a fundamental proof move for list reasoning that is never taught.

The practice level (L10) would be a natural place for this. Instead of another forward-direction proof, L10 could ask: "Given `h : a in l1 ++ l2`, prove `a in l2 ++ l1`." This requires destructuring `h` via `List.mem_append` backwards (getting `a in l1 or a in l2`), then reassembling in the other order. It is still a combination of `mem_cons`/`mem_append`, but exercises the backward direction for the first time.

**Where**: L10 (Practice), or a new level between L06 and L07.

**Effort**: Medium (modifying one level).

**Recommend**: Yes. The learner exits this world able to prove membership but unable to *use* a membership hypothesis, which is the more common situation in downstream proofs.

---

### 5. The `simp` tactic is introduced in L09 (Nodup) as a side tool but never explicitly taught

**What**: L09 introduces `simp` as a `NewTactic` and provides a `TacticDoc`. But in the level itself, `simp` is used to dispatch concrete non-membership goals (`1 not in [2, 3]`) without explanation of what `simp` is doing or why it works here. The introduction does not mention `simp` at all -- the learner encounters it only in hints.

**Why**: `simp` is arguably the most important tactic in the entire mathlib ecosystem, and its introduction in this course (L1 in the plan's Lean map, first listed for W6) should be a deliberate teaching moment. Using it as a throwaway "just do `simp`" in L09 without explaining *what* `simp` does (simplification using a lemma database, automatically trying relevant lemmas) undersells it. The `TacticDoc` is present but minimal.

This is not a request to add a level. Rather, the introduction or the first hint that mentions `simp` should explain briefly: "The tactic `simp` simplifies the goal using a database of known lemmas. Here, it knows that `1 != 2` and `1 != 3`, so it can evaluate `1 not in [2, 3]` automatically. You will use `simp` extensively in later worlds." Two sentences would suffice.

**Where**: L09 (Nodup), in the introduction or the first hint where `simp` appears.

**Effort**: Low (a few sentences in the introduction).

**Recommend**: Yes. A tactic as important as `simp` should not be introduced silently.

---

### 6. L01 is `rfl` on a definitional equality -- it teaches notation but not a proof move

**What**: L01 proves `[1, 2, 3] = 1 :: 2 :: 3 :: []` via `rfl`. This is valuable for teaching the cons notation, but the learner does not perform any reasoning -- `rfl` on a definitional equality is a zero-step proof.

**Why**: L01 is the entry point of the world. Its job is to introduce the list constructors. The `rfl` proof is appropriate for that job. However, the world's first three levels (L01 = `rfl`, L02 = one `rw`, L03 = `rw` + `left` + `rfl`) form a gentle ramp. The concern is not that L01 is too easy in isolation, but that the transition from L01 to the genuinely substantive levels (L04 onward) may feel abrupt if L02 is also a near-tautology (see suggestion #1).

This is a minor structural observation, not a strong recommendation. If L02 is strengthened per suggestion #1, the ramp from L01 to L03 would be smooth enough.

**Where**: L01 (ListCons).

**Effort**: N/A.

**Recommend**: No action needed if suggestion #1 is adopted. Mentioning for completeness.

---

### 7. The boss conclusion's transfer paragraph is good but could be tighter on the "what would change without order" prompt

**What**: The boss conclusion has a "Transfer to paper proofs" section that maps tactic steps to English sentences. It also has a "What comes next" section that previews multisets and `List.Perm`. However, the first review's suggestion #9 specifically asked for a prompt like "Before moving on, consider: what would change if we stopped caring about the order of elements? What if we also removed duplicates?" -- this explicit prompt is not present.

**Why**: The current conclusion *tells* the learner about the hierarchy. A Socratic question would *engage* the learner with it. The difference is between passive reception ("multisets exist") and active consideration ("what would I lose if I dropped ordering?"). This costs one sentence.

**Where**: L11 (Boss), conclusion.

**Effort**: Low (one sentence).

**Recommend**: Consider. The current foreshadowing is already above average. This would push it from informative to engaging.

---

### 8. L08 (FinIndexing) is a concrete `rfl` -- it demonstrates `List.get` but does not exercise it

**What**: L08 proves `[10, 20, 30].get (1, by norm_num) = 20` via `rfl`. Like L01, it teaches a concept (indexing) through a definitional equality.

**Why**: The first review specifically asked for this level (suggestion #3), and it is well-placed and well-written. The `Fin`-connection is explicitly made in the conclusion. However, the proof itself is `rfl` on a concrete evaluation, which means the learner does not practice any proof move related to `List.get`. A symbolic exercise (e.g., `(a :: l).get (0, ...) = a` using `List.get_cons_zero` or a manual unfolding) would teach the learner to *reason* about indexing rather than merely observe it.

That said, this world is already at 11 levels, and the symbolic version introduces API lemmas (`List.get_cons_zero`, `List.get_cons_succ`) that may be more detail than the plan calls for at this stage. The current level achieves its primary goal: showing that `List.get` uses `Fin` as its index type.

**Where**: L08 (FinIndexing).

**Effort**: Medium (modifying the statement and proof).

**Recommend**: Consider. Only if the world has room for the additional complexity.

---

## Overall impression

The re-authored world is dramatically improved. The seven highest-priority issues from the first review have been addressed: `Nodup` is present, proofs require genuine reasoning, `Fin`-indexing connects back to W1, map membership is proved symbolically, filter avoids the `Prop`/`Bool` confusion, the boss integrates map and filter in a multi-step proof, and the permutation/hierarchy story is foreshadowed. The level ladder now has a clear progression: notation (L01) -> symbolic rewriting (L02-L03) -> membership lemmas with disjunctions/existentials/conjunctions (L04-L06) -> structural properties (L07-L09) -> practice (L10) -> boss integration (L11). The writing quality is consistently high, with useful "in plain language" summaries, honest foreshadowing, and well-targeted hints.

The single most important remaining improvement is **suggestion #4: teaching the backward direction of membership `iff` lemmas**. The world currently teaches the learner to *prove* membership from components but never to *use* a membership hypothesis by destructuring it. Since downstream worlds (especially W6-W8 on finset membership) heavily rely on extracting information from `a in s` hypotheses, the learner should encounter this proof move at the list level first. Modifying L10 to use `rcases` on a membership hypothesis would fill this gap with minimal disruption.
