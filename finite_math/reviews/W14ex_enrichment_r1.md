# W14_ex SumFormula -- Enrichment Review R1

## World summary

6 levels proving Gauss's formula `2 * sum_{i=0}^{n} i = (n+1)*n` by induction on natural numbers. The world follows the plan exactly: concrete verification (L01-L02), base case (L03), inductive step (L04), full proof (L05), transfer (L06). This is an Example world building on W14 (induction on range sums).

---

## Ranked suggestions

### 1. L02 is pedagogically redundant with L01

**What**: L01 and L02 both ask the learner to verify the formula for a specific `n` using `norm_num [Finset.sum_range_succ, Finset.sum_range_zero]`. The plan says L01 should verify "for n = 0, 1, 2, 3, 4" -- implying multiple values in one level or across the first two levels. But L01 verifies n=4 and L02 verifies n=2. Both are solved by the identical one-liner. The learner gains nothing from the second that the first did not already provide.

**Why**: The plan allocates L02 to "State the theorem" (writing the formal statement), which is a genuinely different skill -- translating mathematical notation into Lean syntax. The current L02 wastes a level slot on pure repetition and misses the statement-writing exercise entirely.

**Where**: L02 should be replaced with the planned "state the theorem" level, where the learner is given the mathematical formula and must fill in the Lean statement `2 * (sum i in Finset.range (n + 1), i) = (n + 1) * n`. Alternatively, merge the n=2 check into L01 (as a second `Statement` or a remark in the conclusion) and shift L02 to statement-writing.

**Effort**: Medium (rewrite one level)

**Recommend**: Yes -- the current L02 is a plan deviation that eliminates an important pedagogical step (learning to formalize a mathematical statement in Lean).

---

### 2. Missing: the Gauss anecdote and historical motivation

**What**: The world title and L05's conclusion mention "Gauss's formula" but never tell the famous anecdote (young Gauss summing 1 to 100 by pairing terms). This is one of the most famous stories in mathematics and directly motivates *why* the formula works.

**Why**: The pairing argument (1+100 = 2+99 = ... = 50+51 = 101, so the sum is 50*101 = 5050) gives a *second proof* that is conceptually different from induction. Mentioning it would: (a) provide motivation and historical grounding, (b) show the learner that the inductive proof is not the only way to see this, (c) connect to the "why does the formula have n(n+1)/2?" question that the world never answers. The world proves the formula is correct but never explains *why* it should be true.

**Where**: L01 introduction (the opening of the world) is the natural place. A 3-4 sentence version of the Gauss story, plus a one-sentence preview: "We will prove the formula by induction rather than the pairing argument, but the pairing idea explains where the formula comes from."

**Effort**: Low (add a paragraph to L01's introduction)

**Recommend**: Yes -- the formula's most famous motivation is absent from the world that proves it.

---

### 3. L02 manual unfolding is taught but never actually required

**What**: L02's introduction explains how to manually unfold with repeated `rw [Finset.sum_range_succ]` then `rw [Finset.sum_range_zero]` then `rfl`, but the level can be solved with the same one-liner as L01. The manual approach is never forced or isolated.

**Why**: The manual unfolding technique is directly relevant to L03/L04 -- the base case uses `rfl` after the sum reduces, and the inductive step starts with `rw [Finset.sum_range_succ]`. If the learner never practices the manual approach, the transition to L03-L04 is less smooth. The best place to practice "peel off the last term with `sum_range_succ`" is in a concrete level where the learner can see exactly what happens at each step.

**Where**: If L02 is kept as a concrete verification (rather than being replaced per suggestion #1), it should disable `norm_num` so the learner must use the manual unfolding approach. This makes L02 genuinely different from L01. Alternatively, if L02 becomes the statement-writing level per suggestion #1, add a remark in L01's conclusion showing the manual unfolding as an alternative approach.

**Effort**: Low (add `norm_num` to DisabledTactic on L02, or restructure per suggestion #1)

**Recommend**: Yes -- if L02 stays as a verification level, it must be differentiated from L01.

---

### 4. The division-avoidance design choice is mentioned too late and too briefly

**What**: The world uses `2 * sum = (n+1) * n` instead of `sum = n*(n+1)/2` to avoid natural-number division. This clever design choice is explained in L04's conclusion (line 85-87) but never in the introduction or the level where the learner first encounters the statement.

**Why**: A learner seeing `2 * (sum ...) = (n+1) * n` for the first time will wonder "why not just write n*(n+1)/2?". This is a teaching moment about natural-number arithmetic in Lean (division truncates, so `5/2 = 2` in Nat, making `n*(n+1)/2` unreliable). Addressing it early prevents confusion and teaches a transferable Lean skill. The explanation in L04's conclusion is good but arrives after the learner has already been puzzled for 3 levels.

**Where**: L01 introduction, right after stating the formula as `2 * sum = (n+1)*n`. A 2-3 sentence explanation: "In Lean's natural numbers, division truncates: `5 / 2 = 2`, not `2.5`. So `n * (n+1) / 2` would give wrong results for odd `n`. Multiplying both sides by 2 avoids this entirely."

**Effort**: Low (add a paragraph to L01's introduction)

**Recommend**: Yes -- this is a recurring Lean-on-Nat pattern that the learner should internalize.

---

### 5. L06 transfer level is identical to L05

**What**: L06 asks the learner to prove exactly the same statement as L05, with identical hints and identical model solution. The only difference is the introduction, which shows the paper proof and the Lean-paper correspondence table. The learner literally types the same proof twice.

**Why**: Repetition has pedagogical value only when the repeated task is done under different conditions (from memory, under time pressure, with scaffolding removed). L06 does remove the detailed step-by-step hints from L05, but the hidden hints still guide the learner to the identical proof. A stronger transfer exercise would: (a) change the formula slightly (e.g., sum of first n odd numbers = n^2) so the learner must *adapt* the template rather than just replay it, or (b) present the paper proof and ask the learner to identify which Lean tactic corresponds to each step (a matching exercise, not a re-proving exercise), or (c) at minimum, remove the hidden hints entirely so the learner truly works from memory.

**Where**: L06. The best option is (a): change L06 to a different sum identity (e.g., `sum i in range (n+1), (2*i+1) = (n+1)^2`) with the introduction saying "Use the same template you learned for Gauss's formula." This tests transfer because the structure is the same but the details differ. Option (c) is the minimum: remove all Hint lines from L06.

**Effort**: Medium-High for option (a) (new statement, new proof), Low for option (c) (delete hints)

**Recommend**: Yes -- the current L06 is not a genuine transfer exercise, it is a verbatim replay.

---

### 6. Missing: why `Nat.mul_add` is needed (the `rw [ih]` failure without it)

**What**: L04 tells the learner to use `rw [Nat.mul_add]` but never explains *why* `rw [ih]` would fail without it. The learner is told to distribute but not shown what goes wrong if they skip that step.

**Why**: Understanding *why* rewriting sometimes fails is a critical Lean skill. If the learner tries `rw [ih]` on `2 * (sum + (n+1))` without first distributing, the rewrite fails because `ih` matches `2 * sum`, which is not a subexpression of `2 * (sum + (n+1))` -- it is buried inside the multiplication. This is the "rewriting under a function application" issue that trips up many beginners. A brief explanation would teach the general principle: "rw can only match top-level structure of subexpressions. If the pattern is inside `f(...)`, you may need to simplify first."

**Where**: L04 introduction or first hint, as a 2-3 sentence explanation. Something like: "If you try `rw [ih]` directly, it fails. Why? Because the goal has `2 * (sum + (n+1))`, and the hypothesis matches `2 * sum`. But `2 * sum` is not a subexpression -- Lean sees `2 * (sum + (n+1))`, not `(2 * sum) + ...`. Distributing with `Nat.mul_add` first exposes the `2 * sum` subexpression."

**Effort**: Low (add a paragraph to L04's introduction)

**Recommend**: Yes -- this teaches a transferable rewriting skill.

---

### 7. No `NewTactic` or `NewLemma` declarations anywhere

**What**: None of the 6 levels declare any `NewTactic`, `NewLemma`, or `NewDefinition` items. The world introduces `ring` (L04-L05), `Nat.mul_add` (L04), and uses `Finset.sum_range_succ` and `Finset.sum_range_zero` throughout. These should be declared so the game's inventory system tracks them.

**Why**: The game framework uses these declarations to build the tactic/lemma panel that players can reference. Without them, a learner who forgets `Finset.sum_range_succ` has no in-game reference. Since this is an Example world building on W14 (which presumably introduced these lemmas), the world should at minimum declare `NewLemma Nat.mul_add` and `NewTactic ring` if those are first introduced here, or `OnlyTactic`/`OnlyLemma` to constrain what is available.

**Where**: All levels. Add appropriate `NewLemma` and `NewTactic` declarations. Check what W14 introduced and only re-declare items that are new in this world.

**Effort**: Low (add declaration lines)

**Recommend**: Yes -- missing inventory declarations degrade the player experience.

---

### 8. The `range (n + 1)` vs `range n` indexing is silently confusing

**What**: The mathematical formula sums from `i = 0` to `i = n` (inclusive), which is `n+1` terms, encoded as `Finset.range (n + 1)`. But the plan says "sum_{i=0}^{n-1} i = n(n-1)/2". The world actually proves a different (equivalent) formula. The learner is never shown the connection between "sum from 0 to n" and `Finset.range (n+1)`, nor is the off-by-one nature of `range` made explicit.

**Why**: The `range n = {0, 1, ..., n-1}` convention is a common source of confusion. An explicit remark like "Remember: `range n` contains `n` elements, from `0` to `n-1`. So to sum from `0` to `n`, we use `range (n+1)`" would prevent silent confusion. The plan's formula (`n(n-1)/2` for `range n`) and the world's formula (`(n+1)*n` for `range (n+1)`) are equivalent but look different, which could confuse a learner comparing them.

**Where**: L01 introduction or L03 introduction, as a 1-2 sentence remark.

**Effort**: Low (add a remark)

**Recommend**: Consider -- this depends on how much W14 already explains `range`.

---

### 9. Consider a "what if we used integers?" remark

**What**: The entire world works in `Nat` and uses the `2 * sum = (n+1)*n` formulation to avoid division. A brief remark about how the proof would look in `Int` or `Rat` (where you could write `sum = n*(n+1)/2` directly) would round out the mathematical picture.

**Why**: The learner might wonder if the `2*` trick is always necessary. Mentioning that in `Int` or `Rat` you could state `sum = n*(n+1)/2` directly, but then you'd need coercions (`(n : Int)`) and the proof would be messier for different reasons, helps the learner understand the trade-off. This is a depth opportunity that costs almost nothing.

**Where**: L05 conclusion or L06 conclusion, as a 2-3 sentence remark.

**Effort**: Low (add a remark)

**Recommend**: Consider -- nice for depth but not essential.

---

### 10. L03 base case is trivially `rfl` with no scaffolding opportunity

**What**: L03 proves `2 * (sum i in range 1, i) = 1 * 0` and the answer is just `rfl`. The level exists only to isolate the base case, but the base case is so trivial that no skill is practiced.

**Why**: The base case for Gauss's formula is genuinely trivial (both sides are 0). But the level could still teach something: the learner could be asked to *show* that `sum i in range 1, i = 0` first (using `sum_range_succ` and `sum_range_zero`), and then conclude `rfl`. This would reinforce the sum-unfolding from L01-L02 and make the level non-trivial. Alternatively, the level could ask the learner to prove the base case as part of the full induction (i.e., `induction n with | zero => rfl | succ => sorry`) so they practice *setting up* the induction even if the base case itself is easy.

**Where**: L03. Either add a preliminary `have` step, or reformulate as a "set up the induction and prove the base case, leave the inductive step as sorry."

**Effort**: Medium (rewrite the level's proof structure)

**Recommend**: Consider -- the level works as-is but could teach more.

---

## Overall impression

The world is clean, well-structured, and follows a solid pedagogical arc from concrete to abstract to transfer. The Lean code compiles, the disabled tactics are appropriate, and the mathematical content is correct. The strongest aspect is the careful avoidance of natural-number division and the clear explanation of the inductive step's algebra in L04.

The single most important improvement is **replacing L02 with the planned statement-writing level** (suggestion #1). The plan explicitly allocates L02 to statement writing, which is a distinct and valuable skill. The current L02 is a near-duplicate of L01 that wastes a level on repetition. Combined with suggestion #5 (making L06 a genuine transfer exercise rather than a verbatim replay of L05), these two changes would eliminate the world's main weakness: two of its six levels teach nothing new. A world where 4/6 levels are genuinely distinct is significantly weaker than one where 6/6 are.
