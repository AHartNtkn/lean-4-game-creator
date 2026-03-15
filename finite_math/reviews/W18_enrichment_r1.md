# W18 BinomialCoefficients — Enrichment Review (Round 1)

**World**: BinomialCoefficients (W18, Lecture, 9 levels)
**World promise**: The learner understands `Nat.choose`, can compute specific values, and can prove Pascal's rule and basic identities.

---

## Ranked suggestions

### 1. The choose-factorial formula is never mentioned or connected

**What**: The world introduces `Nat.choose` purely through its recursive definition and never mentions the closed-form formula C(n,k) = n! / (k! * (n-k)!), nor the connection `Nat.choose n k = n.descFactorial k / k!`. W17 just taught factorials and descending factorials, so the learner has all the pieces — but the world never connects them.

**Why**: This is the most famous formula for binomial coefficients. A student leaving this world should know both the recursive characterization (Pascal's rule) and the factorial characterization. The formula also explains *why* symmetry holds: swapping k and (n-k) in the denominator. Without it, the learner has a recursive procedure but no closed-form mental model. This is a genuine mathematical depth gap.

**Where**: New level between L06 (Symmetry) and L07 (Counting Subsets), or as an enrichment in L07. The level could state `Nat.choose n k * k.factorial = n.descFactorial k` (avoiding division on naturals) and have the learner apply the mathlib lemma `Nat.choose_mul_factorial_mul_factorial` or `Nat.choose_symm_diff`. At minimum, the introduction or conclusion of L06 should mention the formula and explain why symmetry follows from it.

**Effort**: High (new level) or medium (enrichment paragraph in L06 conclusion)

**Recommend**: Yes

---

### 2. L04 (Pascal's Rule) proves a trivial instance rather than teaching the rule as a proof move

**What**: L04 asks the learner to prove `choose (n+1) 1 = choose n 0 + choose n 1`, which is a single `rw [Nat.choose_succ_succ]`. The plan says the level should "State and prove Pascal's rule," but the world uses Pascal's rule as a *given lemma* rather than having the learner prove it or use it non-trivially. The level titled "Pascal's rule" teaches nothing beyond what L01 already demonstrated.

**Why**: The learner already used `choose_succ_succ` as a rewrite in L01 (6 times). L04 adds no new skill — it is a one-step application of the same rewrite on a different input. This is a missed opportunity to teach Pascal's rule as a *proof ingredient* rather than a rewrite target. A stronger level would ask the learner to derive a two-step consequence of Pascal's rule (e.g., `choose (n+2) 2 = choose n 0 + 2 * choose n 1`, which requires applying Pascal's rule twice and doing arithmetic) or to prove Pascal's rule *itself* by induction from the boundary conditions.

**Where**: L04

**Effort**: Medium (rewrite the level statement and proof)

**Recommend**: Yes

---

### 3. L07 (Counting Subsets) uses `choose_one_right` but never teaches the combinatorial interpretation

**What**: The plan says L07 should "explain that choose n k counts k-element subsets of an n-element set" (coverage item T7(I)). The actual level proves `choose n 1 = n` using the library lemma `choose_one_right` in a single `rw` step. The introduction mentions the counting interpretation in prose, but the proof itself has nothing to do with subsets — it is a rewrite. The transfer moment in the conclusion is about the *algebraic* identity `choose n 1 = n`, not about counting.

**Why**: T7(I) is the *introduction* of the transfer item "counting subsets." This is supposed to be the moment where the learner first connects the abstract `Nat.choose` to a concrete counting problem. A one-step rewrite does not achieve that. A better level would involve `Finset.card (Finset.powersetCard k (Finset.range n))` or a concrete subset-counting statement that links `choose` to actual finset operations.

**Where**: L07

**Effort**: High (redesign the level to involve actual finset subset counting)

**Recommend**: Yes

---

### 4. The boss level is too easy and does not integrate the world's content

**What**: The boss proves `choose n 1 = n` by induction. This is the same result that L07 closed with a library lemma. The boss uses exactly the same lemmas from L01-L02 (choose_succ_succ, choose_zero_right, choose_zero_succ) plus induction. It never touches symmetry (L06), the k > n case (L03), the row sum (L08), or counting subsets (L07). The plan says the boss should be "a non-trivial identity using Pascal's rule and induction" and should integrate M27, M28, and M30 — but it only integrates M28.

**Why**: A boss that only uses material from the first two levels does not validate the learning from the rest of the world. The coverage items say M28(G) and M30(G) — the boss must exercise both Pascal's rule and symmetry at the "generalize" level. A stronger boss would prove an identity that requires *both* Pascal's rule and symmetry, such as `choose n k + choose n (k+1) = choose (n+1) (k+1)` in a less trivial configuration, or the absorption identity `(k+1) * choose n (k+1) = (n-k) * choose n k`, or `choose (2*n) n` is even for n >= 1.

**Where**: L09

**Effort**: High (redesign the boss statement)

**Recommend**: Yes

---

### 5. L02 has a pedagogically awkward `show (3 : Nat) = 2 + 1 from rfl` workaround

**What**: To apply `Nat.choose_zero_succ` to `Nat.choose 0 3`, the level forces the learner to write `rw [show (3 : Nat) = 2 + 1 from rfl, Nat.choose_zero_succ]`. This `show ... from rfl` pattern is never taught and is not in the learner's inventory. It appears again in L09 (boss).

**Why**: This is an implicit skill (per the enrichment reviewer lens on Lean/tactic depth). The learner encounters a new pattern (`show ... from rfl` to reshape a numeral for pattern-matching) without any explanation of *why* it is needed or how it works. The introduction should explain that Lean's numeral representation sometimes prevents lemma matching, and that `show` can bridge the gap. Alternatively, the level could use `norm_num` or `omega` to close the residual goal, or the statement could be designed to avoid the issue (e.g., use `Nat.choose 0 (k + 1)` with `k = 2` as a hypothesis).

**Where**: L02 (and L09 inherits the same issue)

**Effort**: Medium (explain the pattern or redesign to avoid it)

**Recommend**: Yes

---

### 6. No level asks the learner to *derive* a boundary identity — all are given as library lemmas

**What**: L02 introduces `choose_self`, L03 introduces `choose_eq_zero_of_lt`, L06 introduces `choose_symm`, L07 introduces `choose_one_right`, L08 introduces `sum_range_choose`. In every case, the lemma is given and the learner applies it via `rw` or `exact`. No level asks the learner to *prove* a boundary identity from the recursive definition, except the boss.

**Why**: This is the "derivable results presented as axioms" pattern. The world has 9 levels but only the boss involves actual reasoning. Levels 2-8 are all "apply the library lemma." The learner is accumulating API knowledge without building proof skills. At least one mid-world level should require a multi-step derivation — for example, proving `choose_self` by induction using only `choose_succ_succ`, `choose_zero_right`, and `choose_zero_succ`.

**Where**: L02 or a new level after L02

**Effort**: Medium (rewrite one existing level) or high (add a new level)

**Recommend**: Yes

---

### 7. The row sum level (L08) is a single `exact` — zero proof work

**What**: L08 asks the learner to prove `sum m in range 5, choose 4 m = 2^4` and the entire proof is `exact Nat.sum_range_choose 4`. The learner types one line.

**Why**: This is the same pattern as L07 but worse — the identity is deep and beautiful, and the level reduces it to invoking a library lemma. The introduction explains *why* the identity holds (combinatorial counting, setting x=1 in the binomial theorem, induction) but the learner never does any of that. A better version would have the learner prove the row sum for a specific small n (e.g., n=3) by explicitly computing the sum, *then* state the general identity as a theorem. Or better yet, prove the n=0 and inductive-step structure of the general proof.

**Where**: L08

**Effort**: Medium (redesign to require computation or multi-step proof)

**Recommend**: Yes

---

### 8. Missing foreshadowing of the binomial theorem

**What**: The world's conclusion (L09) mentions W18_ex (Pascal's triangle row by row) and the binomial theorem as "what comes next," but never previews *what* the binomial theorem says or why it matters. The row sum identity (L08) is actually a special case of the binomial theorem (set a=b=1), but this connection is never made.

**Why**: This is a cross-world foreshadowing opportunity (category 5). A sentence in L08's conclusion like "This row sum identity is actually a special case of a much more powerful result: the binomial theorem, which tells you what `(a + b)^n` expands to. Setting `a = b = 1` recovers the row sum" would seed the concept and give the learner a reason to care about W19. It costs one sentence.

**Where**: L08 conclusion

**Effort**: Low (one sentence)

**Recommend**: Yes

---

### 9. The `omega` tactic is used in L03 and L06 but never declared via `NewTactic`

**What**: L03 introduces `omega` with a `TacticDoc` entry but no `NewTactic omega` declaration. L06 uses `omega` without any declaration at all. The game framework may display `omega` as available without marking it as newly introduced.

**Why**: This is a consistency issue. The world should have `NewTactic omega` in L03 (where it first appears) so the game UI properly signals it as a new tool. Other worlds in this course consistently pair `TacticDoc` with `NewTactic`.

**Where**: L03

**Effort**: Low (add one line)

**Recommend**: Yes

---

### 10. L05 (Pascal in Action) is nearly identical to L01 in proof technique

**What**: L05 proves `choose 6 2 = choose 5 1 + choose 5 2` with a single `rw [choose_succ_succ]`. L01 already demonstrated `rw [choose_succ_succ]` six times. The only difference is that L05 stops after one rewrite instead of fully unfolding.

**Why**: The plan says L05 should be a "concrete application" of Pascal's rule (coverage M28(S), E17(I)). But the level teaches nothing new beyond L01. A better version would have the learner do a multi-step computation that requires combining Pascal's rule with boundary lemmas in a less rote way — for example, computing `choose 5 2` from scratch by building up through Pascal's triangle step by step, using `have` to name intermediate results.

**Where**: L05

**Effort**: Medium (redesign to be genuinely different from L01)

**Recommend**: Consider

---

### 11. No "what if" or misconception-probing beyond L03

**What**: L03 addresses the C10 misconception (`choose n k = 0` when k > n). But the world has no other misconception or "what if" levels. For instance, learners often assume `choose n k = choose n (k-1) + 1` (confusing Pascal's rule with something simpler), or assume symmetry holds without the `k <= n` constraint.

**Why**: Misconception levels build mathematical maturity (category 4 in the enrichment framework). A level that asks "Is `choose n k = choose n (k-1) + 1` true?" and has the learner disprove it with a counterexample would deepen understanding of Pascal's rule. Similarly, asking what happens when you try to apply `choose_symm` without the `k <= n` hypothesis would reinforce L03's lesson.

**Where**: New level after L06 or as an enrichment in L03

**Effort**: Medium (new level) or low (enrichment paragraph)

**Recommend**: Consider

---

### 12. The naming convention "choose_succ_succ" is never explained

**What**: The learner uses `Nat.choose_succ_succ` repeatedly but the name is opaque. Why "succ_succ"? Because both arguments are in successor form: `(n+1)` and `(k+1)`. This naming convention (`_succ` = "the argument is a successor") is a mathlib pattern that appears throughout the library.

**Why**: This is a Lean-expression layer opportunity. Explaining the naming convention once — in L01 or L04 — would help the learner predict future lemma names (e.g., `add_succ`, `succ_mul`). It costs one paragraph in an introduction.

**Where**: L01 introduction or L04 introduction

**Effort**: Low (one paragraph)

**Recommend**: Consider

---

## Overall impression

The world has a clean level ladder with good mathematical scope — it covers boundary values, Pascal's rule, symmetry, counting, and the row sum, all in 9 levels. The introductions are well-written with clear LaTeX, the conclusions provide good summaries, and the L03 misconception level is well-placed. The disabled tactic set is correct.

The single most important improvement is that **too many levels are single-step library lemma applications**. Levels 04, 05, 07, and 08 each require one `rw` or `exact` call. The learner is reading about deep mathematics but proving trivial goals. The world needs at least 2-3 levels where the learner constructs a multi-step argument — proving `choose_self` by induction, deriving the factorial formula, or computing a row sum explicitly. The boss compounds this problem by also being a relatively easy induction that only exercises L01-L02 material. The world reads more like an API tour than a proof-skills workshop. Restructuring 2-3 existing levels to require genuine multi-step reasoning, and strengthening the boss to integrate symmetry, would transform this from a competent reference world into a genuinely educational one.
