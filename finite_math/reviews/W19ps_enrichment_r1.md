# W19_ps CombinatorialPset — Enrichment Review Round 1

## Ranked suggestions

### 1. L04 does not match the plan; the substitution (1,2) is not the plan's (1,1) row-sum retrieval

**What**: The plan says L04 should "set a = 1, b = 1 in the binomial theorem to get the row-sum." The implementation instead uses x = 1, y = 2 to get 3^n = sum 2^(n-k) C(n,k). This means the row-sum identity is never directly retrieved as a specialization exercise in this pset — it only appears in L05 as a side discussion.

**Why**: The plan chose (1,1) deliberately so the pset retrieves M29 on the *simplest* specialization (the row sum). The current (1,2) substitution is fine mathematically, but it means the learner never actually performs the x=y=1 specialization themselves in this pset. That is a retrieval gap: the most canonical and important specialization is only discussed in prose, never executed. Meanwhile, L04 partially duplicates the boss (L07 uses x=3, y=1; L04 uses x=1, y=2 — both are "substitute into add_pow and simplify one_pow/mul_one" exercises with nearly identical proof structures).

**Where**: L04 (BinomialSpecialization)

**Effort**: Medium — change the statement to the (1,1) specialization and adjust the proof/text accordingly.

**Recommend**: Yes

---

### 2. L01 is a single `rw` and L02 is a single `rw` + `omega`; these are too thin for a pset

**What**: L01 and L02 are each solvable in a single tactic application. For a problem set that is supposed to test retrieval with "reduced scaffolding," these offer no meaningful retrieval challenge — the learner either remembers the lemma name or doesn't, and the proof is one line either way.

**Why**: A pset level should require the learner to compose at least two moves, not just recall a lemma name. The lecture worlds W18 and W19 already have levels that are one-step applications of Pascal's rule and symmetry. The pset should present these in a context that requires combining the skill with something else. For example, L01 could ask the learner to compute C(8,3) from its Pascal decomposition *and then* numerically verify the result (requiring `rw` followed by `norm_num`), or could require two applications of Pascal's rule in sequence. L02 could combine symmetry with Pascal's rule (e.g., prove C(10,7) = C(9,6) + C(9,7) using symmetry and then Pascal's rule, or vice versa).

**Where**: L01 (FreshPascal), L02 (FreshSymmetry)

**Effort**: Medium — modify the statements to require multi-step proofs.

**Recommend**: Yes

---

### 3. No level asks the learner to identify which specialization produces a given identity

**What**: L06's introduction describes the binomial theorem as an "identity factory" with a table of substitutions, but no level ever asks the learner to *reverse-engineer* the substitution. A high-value transfer exercise would present an identity like "sum_k (-1)^k 3^(n-k) C(n,k) = 2^n" and ask: "What are x and y?" before proving it. This is the actual skill a mathematician needs — not just applying a known substitution, but recognizing that an unfamiliar identity is a binomial-theorem instance.

**Why**: The current pset always tells the learner what substitution to use. The boss (L07) gives the strategy section explicitly: "set x=3, y=1." But real transfer means being able to identify the substitution yourself. A level that presents the identity and asks the learner to figure out (x,y) would exercise genuine problem-solving rather than execution of a given plan.

**Where**: New level, or modify L06 or the boss to withhold the substitution hint initially.

**Effort**: High (new level) or Medium (modify L07's introduction to remove the explicit strategy and let the learner discover it).

**Recommend**: Yes

---

### 4. L03 Vandermonde level is an `exact` one-liner — no retrieval of the convolution structure

**What**: L03 asks the learner to prove C(7,3) = sum over antidiagonal(3) of C(4,i)*C(3,j), and the proof is just `exact Nat.add_choose_eq 4 3 3`. The learner does not interact with the convolution structure at all — they just need to know the API name.

**Why**: The plan says this is "retrieval of M31" but the level tests lemma-name recall, not understanding. A richer version would require the learner to first identify that 7 = 4 + 3 (i.e., the statement might say `Nat.choose (4 + 3) 3 = ...` and ask the learner to apply the lemma), or could require working with the expanded sum. Alternatively, the level could ask for a different decomposition (e.g., 7 = 5 + 2) and have the learner instantiate Vandermonde with different parameters, proving they understand the degree of freedom in the decomposition.

**Where**: L03 (SumInvolvingChoose)

**Effort**: Medium — restructure the statement or add a preliminary step.

**Recommend**: Yes

---

### 5. The boss (L07) is structurally identical to L04 — both are "substitute into add_pow, simplify one_pow/mul_one"

**What**: L04 proves 3^n = sum 2^(n-k) C(n,k) via `add_pow 1 2 n` + simplification. L07 proves 4^n = sum 3^k C(n,k) via `add_pow 3 1 n` + simplification. The proof strategy, the simplification steps (one_pow, mul_one), and the structure are identical. The boss is just L04 with different numbers.

**Why**: A boss should require integrating multiple techniques from the world, not repeating a single technique. The plan says L07 should require "multiple techniques" (M28, M29, M31). The current boss only uses M29 (binomial theorem specialization). It does not require Pascal's rule (M28), symmetry (M30), or Vandermonde (M31). A genuine integration boss might ask for an identity that requires specialization *plus* a Pascal's-rule step, or that combines Vandermonde with the binomial theorem.

**Where**: L07 (Boss)

**Effort**: High — design a new boss statement that genuinely integrates multiple coverage items.

**Recommend**: Yes

---

### 6. L05 and L06 are both transfer levels with one-liner Lean proofs — consider merging or differentiating

**What**: L05 proves sum C(6,k) = 64 via `Nat.sum_range_choose 6` (one-liner). L06 proves sum (-1)^k C(5,k) = 0 via `Int.alternating_sum_range_choose_of_ne` (one-liner). Both levels have extensive conclusions discussing transfer but trivial Lean content. Two consecutive one-liner transfer levels feel repetitive as gameplay.

**Why**: The educational value is entirely in the prose (which is good), but the learner's interactive experience is: type one tactic, read text, type one tactic, read text. If one of these were made slightly more challenging (e.g., requiring a small algebraic manipulation before applying the library lemma), the variety of experience would improve. Alternatively, the two transfer discussions could be merged into a single, richer transfer level.

**Where**: L05 (TransferCombinatorialProof), L06 (TransferBinomialTool)

**Effort**: Medium — either merge into one level or add substance to one of the proofs.

**Recommend**: Consider

---

### 7. The conclusion table in L07 references "W18" and "W19" but these world names will mean nothing to the learner

**What**: The conclusion of L07 has a table referencing "From world: W18, W19". The learner sees world names like "BinomialCoefficients" or "BinomialIdentities" in the game, not internal plan IDs like "W18" or "W19".

**Why**: This is a minor polish issue but it breaks immersion. The learner will wonder what "W18" means. Use the actual world display names instead.

**Where**: L07 conclusion

**Effort**: Low — replace "W18" and "W19" with the actual world names.

**Recommend**: Yes

---

### 8. No level in this pset exercises `push_cast`, which was a new tactic introduced in W19

**What**: The plan for W19 introduces `push_cast` (L15) as a new tactic. L07 of this pset uses `push_cast at h` in its proof, but it appears in a hidden hint — the learner is not tested on recognizing when `push_cast` is needed. Since this is the W19 pset, retrieval of `push_cast` would be appropriate.

**Why**: `push_cast` is a genuine pain point when working with binomial sums that cross type boundaries (Nat to Int). If the pset avoids it, the learner never practices this skill in a retrieval context. L04 or the boss could be formulated so that the goal naturally involves a type mismatch requiring `push_cast`.

**Where**: L04 or L07

**Effort**: Medium — reformulate one level's statement to work in `Int` or another type, forcing `push_cast` usage.

**Recommend**: Consider

---

### 9. Missing combinatorial interpretation for L04's identity

**What**: L04 proves 3^n = sum 2^(n-k) C(n,k) but never gives a combinatorial interpretation. Compare L05, which beautifully explains the subset-counting interpretation of the row sum. The 3^n identity also has a natural interpretation: coloring n objects with 3 colors, grouping by which get the "special" color.

**Why**: The course emphasizes dual algebraic/combinatorial perspectives (this is T7). Every specialization level is a chance to exercise this duality. Missing the interpretation for (1,2) while providing it for (1,1) sends an implicit message that not all identities have combinatorial readings — but this one does.

**Where**: L04 conclusion

**Effort**: Low — add a paragraph to the conclusion.

**Recommend**: Consider

---

### 10. L06's paper proof of the alternating sum has a confusing reindexing step

**What**: The paper proof in L06's conclusion says "By reindexing (or noting (-1)^{n-k} = (-1)^n * (-1)^{-k} = (-1)^n / (-1)^k), the identity follows." This uses negative exponents in a way that doesn't actually work cleanly ((-1)^{-k} is not standard in the naturals) and the "reindexing" is left vague.

**Why**: A transfer level's paper proof should be a model the learner can actually imitate. This one has a hand-wavy step that could confuse rather than teach. A cleaner paper proof would note that (-1)^{n-k} = (-1)^n * (-1)^k (since (-1)^2 = 1) and then factor out (-1)^n.

**Where**: L06 conclusion

**Effort**: Low — rewrite the paper proof paragraph.

**Recommend**: Yes

---

## Overall impression

The world fulfills its role as a problem set: it retrieves Pascal's rule, symmetry, Vandermonde, specialization, and provides two transfer discussions. The prose quality is high — the conclusions are thoughtful, the tables are useful reference material, and the "transfer moments" are a consistent and valuable feature.

The single most important improvement is **differentiating the boss from L04**. Currently, L07 and L04 have identical proof structures (substitute into add_pow, simplify one_pow and mul_one). A problem set boss should integrate multiple skills from the world — at minimum Pascal's rule or Vandermonde alongside specialization — rather than repeating the same technique with different constants. Fixing this, along with restoring the plan's intended (1,1) specialization for L04, would give the pset genuine variety and make the boss a true capstone.
