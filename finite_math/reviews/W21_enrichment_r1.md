# W21 FinsuppWorld -- Enrichment Review (Round 1)

## Ranked Suggestions

### 1. L07 does not prove what the plan promises: support of a sum

**What**: The plan says L07 should "Prove `(single a m + single b n).support` for `a ne b`" but the actual L07 proves `(single 1 3 + single 2 5).sum (fun _ m => m) = 3 + 5` -- a summation identity, not a support computation.

**Why**: The plan explicitly lists L07 as covering "Algebraic structure" and M21 (S), meaning it should deepen the learner's understanding of how `Finsupp` support behaves under addition. The actual level is a second `Finsupp.sum` exercise, making it a near-duplicate of L06 in proof pattern (both use `sum_single_index`). The learner never sees `Finsupp.support_add`, never proves a support-of-sum result, and never encounters the subtlety that `support (f + g) ⊆ f.support ∪ g.support` (with potentially strict inclusion when values cancel). This is a genuine coverage gap on M21 (S), and the "algebraic structure" column is undelivered.

**Where**: L07 -- replace the current statement with a support-of-sum proof, e.g., `(Finsupp.single 1 3 + Finsupp.single 2 5).support = {1, 2}`. This would teach `Finsupp.support_add` or the ext-based approach for support equality, and deliver the plan's promise.

**Effort**: High (rewrite the level).

**Recommend**: Yes.

---

### 2. The boss level does not exercise L04, L05, or L07 -- it only tests L01-L03 and L06

**What**: L08 asks for evaluation (`single_apply`), support (`support_single_ne_zero`), and summation (`sum_single_index`) -- all on a single `Finsupp.single 2 7`. It never uses `add_apply` (L04), never uses `mem_support_iff` in a contradiction argument (L05), and never uses `sum_add_index'` (L07).

**Why**: A boss level should integrate the full world. The current boss is essentially three independent one-step exercises glued by `And`. It does not require the learner to chain reasoning across addition, totality, or the sum-distributes-over-addition pattern. A learner who skipped L04, L05, and L07 would pass the boss unchanged.

**Where**: L08 -- redesign the boss to require multi-step reasoning involving addition. For example: define `f = single 1 3 + single 2 5`, prove `f 1 = 3` (uses `add_apply` + `single_apply`), prove `1 ∈ f.support` (uses `mem_support_iff`), prove `f.sum (fun _ m => m) = 8` (uses `sum_add_index'` + `sum_single_index`). This forces the learner to deploy skills from L04, L05, L06, and L07.

**Effort**: High (rewrite the level).

**Recommend**: Yes.

---

### 3. Missing: what happens when you `single a 0`?

**What**: Add a level (or extend L03) that explores the edge case `Finsupp.single a 0`. Its support is empty (`support_single_zero`), and `(Finsupp.single a 0) = 0` (the zero `Finsupp`).

**Why**: The side condition `b != 0` in `support_single_ne_zero` is stated but never tested against its failure case. The learner never sees that `single a 0` is the zero function, which is a mathematically important fact: it means `single` does not always produce a function with `a` in its support. This edge case is exactly the kind that trips up learners who form the mental model "single a b has support {a}" without the `b != 0` caveat. The L06 conclusion mentions `single a 0 = 0` but the learner never proves it or sees the support collapse.

**Where**: New level between L03 and L04 (or extend L03 to a two-part problem). Statement: `(Finsupp.single 3 (0 : N)).support = {}` or equivalently `Finsupp.single 3 (0 : N) = 0`.

**Effort**: Medium (add a small level).

**Recommend**: Yes.

---

### 4. L04 evaluates the sum at only one point -- the "two-point" claim is half-verified

**What**: L04 is titled "A Finsupp nonzero at two points" but the statement only proves `(single 1 3 + single 2 5) 1 = 3`. The learner never proves evaluation at the second point (`(single 1 3 + single 2 5) 2 = 5`), nor that `0` is not in the support.

**Why**: The level's title and introduction promise a two-point `Finsupp`, but the proof only touches one point. The learner does not actually verify the "two-point" nature. Adding a second conjunct (evaluating at `2` to get `5`) would make the level deliver on its title, and the proof would be almost identical to the first part -- reinforcing the `add_apply` + `single_apply` pattern through a second application rather than just one.

**Where**: L04 -- extend the statement to a conjunction: `(single 1 3 + single 2 5) 1 = 3 /\ (single 1 3 + single 2 5) 2 = 5`.

**Effort**: Low-medium (extend the existing statement).

**Recommend**: Yes.

---

### 5. No `Finsupp.zero` level -- the zero function is never explicitly constructed

**What**: Introduce `0 : alpha ->_0 M` as the zero `Finsupp` and show that its support is empty and it evaluates to `0` everywhere.

**Why**: Every monoid needs its identity element to be understood. The learner sees `Finsupp.single` and `f + g` but never meets `0` explicitly. The zero function is needed to understand `single a 0 = 0` (suggestion 3), to make sense of the `h a 0 = 0` side conditions in `sum_single_index` and `sum_add_index'`, and to appreciate that `Finsupp` forms an additive monoid. L01's introduction mentions `0 : alpha ->_0 M` is the zero function, but it is never used in a proof.

**Where**: New level, ideally early (between L02 and L03 or between L03 and L04). Statement options: `(0 : N ->_0 N).support = {}` and/or `(0 : N ->_0 N) 5 = 0`.

**Effort**: Medium (add a new level).

**Recommend**: Consider.

---

### 6. The `->_0` notation is introduced in L01 text but never appears in a goal state

**What**: The notation `alpha ->_0 M` is explained in L01's introduction and documentation, but all 8 level statements use `Finsupp.single` with concrete types -- the learner never actually sees `->_0` in the Lean goal panel.

**Why**: The plan lists N13 (I) for L02, meaning this is where the notation is introduced. But the notation is only used in L04's explicit type annotation `(Finsupp.single 1 (3 : N) + Finsupp.single 2 5 : N ->_0 N)` and L07's similar annotation. These appear as type ascriptions, not in the goal. A learner might read the introduction, hear about `->_0`, and then never see it in practice. A small level or problem where the goal state explicitly involves `f : N ->_0 N` (rather than just `Finsupp.single ...`) would make the notation concrete.

**Where**: Could be incorporated into the zero-function level (suggestion 5) or the `single a 0` level (suggestion 3) by using a variable `f : N ->_0 N` in the statement.

**Effort**: Low (adjust an existing or new level's statement phrasing).

**Recommend**: Consider.

---

### 7. No foreshadowing of polynomials as `Finsupp`

**What**: The L01 introduction mentions polynomials as a motivating example, and the L08 conclusion says "Polynomials (as `Finsupp N R` with a ring structure)." But no level actually connects `Finsupp` to polynomial representation.

**Why**: The polynomial connection is the single most motivating application of `Finsupp`. A brief remark in the L08 conclusion is not enough -- the learner never sees, even informally, that `Finsupp.single 2 3` represents the monomial `3x^2`. Adding one sentence in L04's conclusion (where `single 1 3 + single 2 5` naturally represents `3x + 5x^2`) would make this concrete without requiring a new level.

**Where**: L04 conclusion -- add a sentence like: "In fact, `single 1 3 + single 2 5` is exactly how Mathlib represents the polynomial `3x + 5x^2`: the domain index is the exponent, and the value is the coefficient."

**Effort**: Low (one sentence in a conclusion).

**Recommend**: Yes.

---

### 8. L05 misconception level uses `exact h rfl` without teaching it as a pattern

**What**: L05 teaches the proof-by-contradiction pattern for `a not-in f.support`, culminating in `exact h rfl` to close `h : 0 != 0`. This is a useful proof move but it is not named or highlighted as a reusable pattern.

**Why**: The "derive a contradiction from `h : a != a`" pattern (or more generally `h : x != x`, closed by `exact h rfl`) appears in many Lean proofs. L05 uses it but the hints and conclusion focus on the Finsupp-specific content. Adding one sentence to name this as "the `exact h rfl` contradiction pattern" would help the learner recognize and reuse it.

**Where**: L05 conclusion -- add a brief paragraph naming the pattern.

**Effort**: Low (a sentence in the conclusion).

**Recommend**: Consider.

---

### 9. L06 and L07 side conditions are handed to the learner -- no level isolates proving them

**What**: In L06, the side condition `h a 0 = 0` is closed by `rfl`. In L07, the two side conditions for `sum_add_index'` are closed by `fun _ => rfl` and `fun _ _ _ => rfl`. In both cases, the hint tells the learner exactly what to write. The learner never independently figures out why these conditions hold or what they mean.

**Why**: The side conditions are the mathematically interesting part of `sum_single_index` and `sum_add_index'`. They encode the requirement that `h` is "well-behaved" (sends zero to zero, is additive). If the boss level used a non-trivial `h` (like `fun a m => a * m`, which is already used in L08 part 3), the learner would need to prove `a * 0 = 0` by `ring` rather than `rfl`, forcing engagement with what the side condition means. This is partially addressed in L08 (which uses `ring`), but L06-L07 give no practice.

**Where**: If suggestion 1 is implemented (rewriting L07), the new L07 or the boss could use a function `h` where the side conditions are not `rfl`-closed.

**Effort**: Medium (adjust function choice in a level).

**Recommend**: Consider.

---

### 10. Missing strategy name: the "unfold-then-resolve" pattern for conditionals

**What**: Levels L01, L02, L04, and L05 all follow the same two-step pattern: (1) rewrite with a lemma that introduces an `if-then-else`, (2) resolve the conditional with `if_pos` or `if_neg`. This pattern is never given a name.

**Where**: L02 conclusion, where the pattern has been seen twice and is about to be used repeatedly. Add a sentence like: "This 'unfold-then-resolve' pattern -- rewrite to introduce a conditional, then close it with `if_pos` or `if_neg` -- is one of the most common proof moves when working with piecewise-defined functions in Mathlib."

**Effort**: Low (a sentence in a conclusion).

**Recommend**: Consider.

---

## Overall Impression

The world has a solid pedagogical arc: it introduces `Finsupp` and `single` with clear motivation, builds up evaluation, support, addition, and summation in a logical order, and includes a useful misconception level (L05) that addresses the totality of `Finsupp`. The introductions and conclusions are well-written, with good "plain language" summaries and transfer moments. The disabled tactic list is appropriate.

The single most important improvement is **suggestion 1**: L07 does not deliver what the plan specifies. It should prove a support-of-sum result, not a second summation identity. This is both a plan deviation and a coverage gap -- the learner never reasons about how support interacts with addition, which is arguably the most important structural property of `Finsupp`. Fixing L07 would then naturally feed into a redesigned boss (suggestion 2) that actually integrates the full world rather than testing only L01-L03 and L06.
