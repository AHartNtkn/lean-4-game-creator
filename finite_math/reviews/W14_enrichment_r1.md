# W14 RangeSumInduction — Enrichment Review (Round 1)

**Reviewer**: lean4game-enrichment-reviewer
**World**: W14 RangeSumInduction (Lecture, 9 levels)
**World promise**: The learner can prove equalities about `sum i in range n, f i` by induction, peeling off the last term with `sum_range_succ`.

---

## Ranked suggestions

### 1. L06 deviates from plan: sum of odd numbers replaces sum of i

**What**: L06 was planned as "Sum of i from 0 to n-1: Prove `sum i in range n, i = n * (n-1) / 2`" but was implemented as "Sum of the first n odd numbers: Prove `sum i in range n, (2*i+1) = n^2`."

**Why**: This is not merely a plan deviation — it is actually a pedagogically *better* choice for W14. The sum-of-odds identity `1+3+5+...+(2n-1) = n^2` is a more compelling identity than summing i, it exercises `ring` on a genuinely interesting algebraic step (`n^2 + (2n+1) = (n+1)^2`), and the geometric gnomon interpretation (which the conclusion already includes) adds depth. Meanwhile, the plan explicitly reserves the sum-of-i formula for W14_ex, where it gets a dedicated 6-level treatment. So the deviation is well-motivated. However, the **plan coverage item** for L06 was `E4 (preview)` — a preview of the sum-of-natural-numbers example. The sum-of-odds identity does not preview E4 at all. The conclusion should add a forward-looking sentence connecting to W14_ex: something like "In the next world, you will prove the classic formula for the sum of the first n natural numbers: `sum i in range n, i = n*(n-1)/2`. The proof follows the same template."

**Where**: L06 conclusion text
**Effort**: Low
**Recommend**: Yes

---

### 2. The `ring` tactic is used extensively but never declared as `NewTactic`

**What**: Levels L05, L06, L07, and L09 all require `ring` in their proofs, yet W14 never declares `NewTactic ring`. The plan places `ring`'s official introduction at W15 L04 (coverage item L7). In practice, `ring` was already introduced via `NewTactic` in W8_ex L04 (FinsetExploration), so the learner has it in their inventory. But W14 uses `ring` as a central tool without any explicit acknowledgment that it is being used for the first time in a new context (polynomial arithmetic in inductive steps, as opposed to simple numeric computation).

**Why**: The learner needs to understand that `ring` closes polynomial equalities, not just numeric ones. The first time they see `ring` close `n^2 + (2n+1) = (n+1)^2` (L06) is qualitatively different from using `ring` to compute `1^2 + 2^2 = 5` in W8_ex. This is a genuine capability upgrade that deserves at least a sentence of explanation.

**Where**: L05 introduction or conclusion — this is where `ring` is first needed in W14. Add a brief note: "The `ring` tactic closes equalities that hold in any commutative (semi)ring. You have seen it for numeric computations; here it handles symbolic polynomial identities like `2 * n + 2 = 2 * (n + 1)`."

**Effort**: Low
**Recommend**: Yes

---

### 3. L04 and L07 both prove `sum i in range n, 2 = 2 * n` — the repetition is unmotivated

**What**: L04 re-proves `sum i in range n, 1 = n` (already proved in L03) to teach `calc`. L07 re-proves `sum i in range n, 2 = 2 * n` (already proved in L05) to teach "the inductive step in detail" with `calc`. Two levels re-prove earlier results with no new mathematical content.

**Why**: L04's repetition is justified — it teaches `calc` syntax on a familiar problem, which is standard pedagogical practice. But L07's repetition is weaker: the learner has already seen `calc` in L04 and `ring` in L05-L06. L07 just combines them on a problem they already solved. The "coaching for boss" framing doesn't add enough value because L06 (sum of odds) is already harder than L07's statement.

The opportunity: replace L07's statement with something new that genuinely exercises the `calc` + `ring` combination on a harder identity, or make L07 teach something L06 didn't cover. For example, L07 could prove `sum i in range n, (3*i + 1) = n*(3*n-1)/2` (a pentagonal number formula in Nat form), which would give the learner a new problem requiring a 3-step `calc` with a non-trivial `ring` step, and would preview pentagonal numbers for mathematical culture. Alternatively, if re-proving is the point, L07 should be explicit about *why*: "This is a rehearsal level. The boss will require you to set up a `calc` proof on a new identity. Practice the mechanics here."

**Where**: L07
**Effort**: Medium (rewrite the level with either a new identity or explicit rehearsal framing)
**Recommend**: Yes

---

### 4. No level exercises the case where the base case requires non-trivial arithmetic

**What**: L08 teaches that `range 0 = empty` and `sum over empty = 0`, but every base case in the world has right-hand side `0` at `n = 0`. No level presents a statement where the right-hand side at `n = 0` is non-trivially `0` (e.g., `n*(2*n+1)` becomes `0*(0+1) = 0` which requires `ring` or `omega`, not `rfl`).

**Why**: In real induction proofs, the base case is often not `rfl`. The conclusion of L08 even warns about this: "Understanding this mechanism matters: if the right-hand side does not reduce to `0` at `n = 0`, you may need `range_zero` + `sum_empty` explicitly, followed by arithmetic." Yet no level actually demonstrates this situation. This is a concrete example gap: the world warns about a pitfall but never lets the learner encounter it.

**Where**: L08 would be the natural place — modify it so the base case requires `rw [Finset.range_zero, Finset.sum_empty]` followed by `ring` or `omega`, not just the rewrite. Alternatively, the boss (L09) could have a right-hand side that doesn't reduce by `rfl` at `n = 0`. (Note: the current boss `n*(2*n+1)` does reduce to `0` by `rfl` because `0*(anything) = 0` definitionally in Nat.)

**Effort**: Medium (modify L08 or add a sub-task to L08)
**Recommend**: Yes

---

### 5. The "three-step pattern" is used but never explicitly named as a strategy

**What**: L03's conclusion names the "three-step pattern" (induction / base case / inductive step with `sum_range_succ + ih + ring`), and subsequent levels follow it. But this is described as a "template" in prose — it is never given a sticky name like "the peel-rewrite-close pattern" or "the PSR pattern (Peel, Substitute, Ring)."

**Why**: Naming proof strategies improves retention and transfer. The learner who remembers "peel-rewrite-close" can retrieve the technique later (in W14_ex, W15, W16, even W19) without re-reading the description. A named strategy is also easier to reference in hints: "Use the peel-rewrite-close pattern" is more actionable than "Follow the same template as before."

**Where**: L03 conclusion (where the pattern is first articulated) and L09 conclusion (transfer moment). Introduce a short name and reuse it.

**Effort**: Low
**Recommend**: Yes

---

### 6. L01 is under-utilizing the review opportunity

**What**: L01 proves `(Finset.range 5).card = 5`, which is a single `rw [card_range]`. It is supposed to be a "range recap" but only exercises one fact (`card_range`). The introduction mentions `range_zero` and `mem_range` but neither is used.

**Why**: A review level that mentions three facts but only tests one is a missed opportunity. The learner would benefit from at least a two-part exercise (e.g., prove both `(range 5).card = 5` and `3 in range 5` or `5 not in range 5`). This would reinforce `mem_range` which is not directly used anywhere else in the world but is an important conceptual prerequisite for understanding what `sum_range_succ` is doing (the sum is over elements `i < n`).

**Where**: L01 — either add a second `Statement` or modify the existing one to be slightly richer (e.g., `(Finset.range 5).card = 5 and 3 in Finset.range 5`).

**Effort**: Medium
**Recommend**: Consider

---

### 7. No mention of `Finset.sum_range_zero` as the base-case lemma

**What**: The world uses `range_zero` + `sum_empty` to explain why the base case works, but never mentions `Finset.sum_range_zero` (if it exists in mathlib), which would be a single rewrite. This might simplify base case proofs and is worth at least mentioning.

**Why**: If `sum_range_zero` exists, it collapses the two-step `rw [range_zero, sum_empty]` into a single rewrite, which is cleaner. If it does not exist, the world should note that it's a derived fact (range_zero + sum_empty). Either way, the learner benefits from knowing whether this shortcut exists.

**Where**: L08 conclusion or L03 conclusion
**Effort**: Low (check whether `Finset.sum_range_zero` exists in mathlib; if yes, mention it)
**Recommend**: Consider

---

### 8. The geometric interpretation in L06 deserves visual reinforcement

**What**: L06's conclusion describes the gnomon/L-shape geometric proof of `1+3+5+...+(2n-1) = n^2` but provides no visual or concrete instantiation. Lean4game supports rendering, and even without images, a concrete numerical check (e.g., "Check: 1+3+5 = 9 = 3^2") would ground the abstraction.

**Why**: The geometric proof is one of the most beautiful "proofs without words" in mathematics. The conclusion mentions it but moves on quickly. Adding a concrete numerical example makes the pattern visceral: "For n=4: 1+3+5+7 = 16 = 4^2. The 4th gnomon (7 unit squares) wraps around the previous 3x3 square to make a 4x4 square."

**Where**: L06 conclusion
**Effort**: Low
**Recommend**: Consider

---

### 9. Boss identity `sum (4i+3) = n(2n+1)` has no motivational context

**What**: The boss asks the learner to prove `sum i in range n, (4*i+3) = n*(2*n+1)`. This identity is never motivated — it appears from nowhere, is proved, and disappears. There is no mathematical reason given for why this particular formula matters or where it arises.

**Why**: The learner is more engaged when a boss has *stakes*. Even a single sentence would help: "This identity counts the total number of dots in the first n pentagonal-shaped figures" (it doesn't, but something analogous), or "This identity arises when summing consecutive odd numbers starting from 3" (which is closer to true: 3+7+11+15+... = sum of (4i+3)). If no natural interpretation exists, acknowledge it: "This is a practice identity chosen to exercise your skills — the point is the proof technique, not the formula itself." Transparency about why an identity was chosen is better than no context.

**Where**: L09 introduction
**Effort**: Low
**Recommend**: Consider

---

### 10. Forward-looking connection to `prod_range_succ` in W15

**What**: The world conclusion mentions "The next world will apply these techniques to a specific classic formula" (referring to W14_ex). But W15 (Finset.prod and algebraic manipulation) is also a direct successor, and `prod_range_succ` is the multiplicative analogue of `sum_range_succ`. The conclusion could seed the vocabulary: "The peeling-off lemma `sum_range_succ` has a multiplicative twin: `prod_range_succ`, which you will meet soon."

**Why**: Vocabulary seeding is low-cost and improves transfer. When the learner encounters `prod_range_succ` in W15, they will immediately connect it to what they learned here, reducing cognitive load.

**Where**: L09 conclusion
**Effort**: Low
**Recommend**: Consider

---

## Overall impression

**What the world does well**: The world has a clear, well-paced progression from reviewing `range` (L01) through introducing `sum_range_succ` (L02), teaching the induction template (L03), introducing `calc` (L04), increasing difficulty (L05-L06), and culminating in a boss (L09). The three-step induction pattern is consistently reinforced. L06 (sum of odds = n^2) is an excellent choice that adds mathematical beauty. The transfer moment in the boss conclusion is thorough and well-written. The `calc` introduction in L04 is well-motivated.

**The single most important improvement**: The world warns about non-trivial base cases (L08) but never actually presents one. Every base case in the world closes with `rfl`. This is suggestion #4 above. Making at least one base case require actual work (not just `rfl`) would turn L08 from a "here's what could happen" lecture into a "here's what it feels like" experience. This is the gap between telling the learner about a pitfall and making them encounter it.
