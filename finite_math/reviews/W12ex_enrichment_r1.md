# W12_ex CountingFunctions -- Enrichment Review R1

**Reviewer**: enrichment-reviewer
**World**: CountingFunctions (W12_ex), 5 levels
**Predecessor**: CountingPigeonhole (W12), 10 levels
**Plan reference**: PLAN.md lines 527-537

---

## Ranked suggestions

### 1. The boss level (L05) does not test integration -- it is a near-duplicate of L01

**What**: L05 ("Boss: The multiplication principle") asks the learner to prove `Fintype.card (Fin 2 -> Fin 3) = Fintype.card (Fin 3) * Fintype.card (Fin 3)`. The proof is `rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; norm_num` -- structurally identical to L01, with the only difference being that one `card_fin` rewrite stays on the RHS. This is not a boss; it is a repetition.

**Why**: A boss should integrate the world's lessons. This world teaches four distinct things: total function count (L01), injective count via embeddings (L02), impossibility of surjection (L03), and Bool-function counting with subset connection (L04). A real boss would combine at least two of these. The current L05 combines none -- it only reproves L01 in a trivially different form.

**Where**: L05 (replace or substantially redesign)

**Effort**: High

**Recommend**: Yes

**Concrete suggestion**: Replace L05 with a level that combines results from L01-L03. For example:
- Prove that the number of non-injective functions equals the total minus the injective count: `Fintype.card (Fin 2 -> Fin 3) - Fintype.card (Fin 2 ↪ Fin 3) = 3`. This requires retrieving L01's result (9 total) and L02's result (6 injective), then arithmetic. It also concretizes the complementary counting principle.
- Alternatively, prove something that combines the function-type cardinality with the surjection impossibility, e.g., a statement involving both `Fintype.card_fun` and `Fintype.card_le_of_surjective`.

The conclusion should still contain the transfer moment about the multiplication principle (which is excellent and should be preserved), but the *proof task* should require genuine integration.

---

### 2. Missing: a level that concretely enumerates injective functions or verifies one specific injection

**What**: L02 counts the injective functions abstractly (via `Fintype.card_embedding_eq`) but the learner never constructs or examines a specific injection. Adding a level where the learner defines a specific embedding `Fin 2 ↪ Fin 3` (e.g., mapping 0 to 1 and 1 to 2) would ground the abstract count.

**Why**: The world's purpose is concretization. L01's conclusion lists all 9 functions and L02's conclusion lists all 6 injections -- but these are presented as *text*, not as *proof tasks*. The learner reads about injective functions but never touches one. An example world should make the learner work with at least one specific instance, not just count them abstractly.

**Where**: New level between L02 and L03 (or replacing part of L05 if the boss is redesigned)

**Effort**: High (new level)

**Recommend**: Yes

**Concrete suggestion**: A level where the learner constructs an embedding `Fin 2 ↪ Fin 3` by providing the function and proving injectivity. The proof of injectivity on `Fin 2` can be done by `intro a b; fin_cases a <;> fin_cases b <;> simp` or similar case analysis. This connects back to the `fin_cases` skill from W2 (FinCompute) and makes the abstract count visceral -- the learner sees what "one of the 6" actually looks like.

---

### 3. L03 introduces `Fintype.card_le_of_surjective` but never connects it to its dual `Fintype.card_le_of_injective`

**What**: L03 uses `Fintype.card_le_of_surjective` to show no surjection exists from `Fin 2` to `Fin 3`. The dual fact -- `Fintype.card_le_of_injective`, which the learner already knows from W12 -- goes unmentioned. The symmetry between "injections need |domain| <= |codomain|" and "surjections need |codomain| <= |domain|" is stated in the conclusion table but never turned into a proof task.

**Why**: This is a "derivable relationship presented passively" situation. The conclusion's pigeonhole/reverse-pigeonhole table is excellent exposition, but the learner would benefit from proving the dual direction as well -- or at least seeing both lemmas side by side in a proof. Since L02 already showed that injective functions *do* exist from `Fin 2` to `Fin 3`, a natural question is: "The cardinality bound for injections is satisfied (2 <= 3), so injections exist. The cardinality bound for surjections is *not* satisfied (3 > 2), so surjections cannot exist." This two-sided observation connects L02 and L03 in a way the current world does not exploit.

**Where**: L03 conclusion (add explicit reference to `Fintype.card_le_of_injective` and the dual reasoning), or a short extra level

**Effort**: Low to medium

**Recommend**: Consider

---

### 4. L04 introduces the `alpha -> Bool` / subset / power set connection but never formalizes it

**What**: L04's conclusion beautifully explains that functions `Fin 3 -> Bool` correspond to subsets of `Fin 3`, and that `2^n` is why the power set is denoted `2^alpha`. But the learner never proves anything about this correspondence. The level is just another cardinality computation (structurally identical to L01, with `card_bool` instead of `card_fin`).

**Why**: The functions-to-Bool / subsets bijection is one of the most important conceptual connections in combinatorics. Simply counting `2^3 = 8` does not teach this connection -- it only verifies a number. An example world should make the learner *experience* the bijection, not just read about it.

**Where**: L04 (modify to include a proof element involving the bijection), or a new level after L04

**Effort**: Medium to high

**Recommend**: Consider

**Concrete suggestion**: After the cardinality computation, add a level (or extend L04) where the learner proves that a specific function `f : Fin 3 -> Bool` (e.g., `f = ![true, false, true]`) corresponds to a specific `Finset (Fin 3)` (namely `{0, 2}`). This would use `Finset.filter` or the `Set.indicator` / `Finset.indicator` machinery. Even a simple `decide`-based proof would make the connection concrete rather than purely narrative.

---

### 5. The plan calls for a "Transfer: The multiplication principle" level (L05) but the current L05 is a computation, not a transfer

**What**: The plan's L05 entry says: "State why `|Fin 2 -> Fin 3| = 3^2` in ordinary language" with coverage item T1 (R). The actual L05 is a `rw`/`norm_num` proof with a transfer moment in the *conclusion text*. The transfer is passive (read-only) rather than active.

**Why**: Transfer levels in other worlds (e.g., W3_ex L11, W4_ex) have the learner actively restate or reformulate, not just solve a Lean proof and then read a paragraph. If the world's promise includes transfer, the transfer should be a proof task or at minimum an interactive element, not a conclusion paragraph tacked onto a computation that is unrelated to transfer.

**Where**: L05 (redesign)

**Effort**: Medium (if the boss is already being redesigned per suggestion 1, this can be folded in)

**Recommend**: Yes

**Concrete suggestion**: If the boss is redesigned per suggestion 1, make the current L05's excellent transfer text the conclusion of the redesigned boss. Alternatively, add a dedicated transfer level where the statement itself encodes the multiplication principle in a more "linguistic" form -- e.g., proving `Fintype.card (Fin m -> Fin n) = n ^ m` for general `m` and `n` (using `Fintype.card_fun` and `Fintype.card_fin`), with the introduction asking the learner to articulate *in words* why this formula holds before proving it formally. The generalization from specific (2, 3) to general (m, n) is itself a transfer skill.

---

### 6. No level uses `omega` in a way that connects counting to contradiction -- missed proof-move reinforcement

**What**: L03 uses `omega` to close the contradiction `3 <= 2`. But this proof move -- "derive a false arithmetic inequality from a counting argument, then close with `omega`" -- is never named as a strategy. The W12 predecessor world (L05, L07, L08, L09) also uses this move repeatedly, but by the time W12_ex L03 does it again, it could be named: "the counting contradiction pattern."

**Why**: Naming proof strategies aids transfer. The learner has now seen this pattern at least 4-5 times across W12 and W12_ex. A sentence in L03's introduction or conclusion naming it would cost nothing and help the learner recognize the pattern in future worlds.

**Where**: L03 introduction or conclusion (add a sentence)

**Effort**: Low

**Recommend**: Consider

---

### 7. Cross-world foreshadowing: no mention of where function-counting reappears

**What**: The plan shows that function-type cardinality (M14) reappears in W12_ps (retrieval), W21 (Finsupp), and W22/W23 (permutations/binomial). The world conclusion mentions the multiplication principle abstractly but does not hint that this counting skill will be needed again.

**Where**: L05 conclusion (add one sentence)

**Effort**: Low

**Recommend**: Consider

**Concrete suggestion**: Add to the boss conclusion something like: "The exponential counting of function types will reappear when we count permutations, subsets, and binomial coefficients -- the same multiplication principle in increasingly sophisticated settings."

---

## Overall impression

**What the world does well**: The narrative arc is clear and well-structured. The introductions and conclusions are excellent -- the enumeration tables in L01/L02 conclusions, the pigeonhole/reverse-pigeonhole duality table in L03, and the functions-to-subsets connection in L04 are all high-quality exposition. The disabled-tactic set is appropriate. The proof steps are well-hinted and scaffolded. The world correctly introduces `Fintype.card_embedding_eq`, `Nat.descFactorial`, and `Fintype.card_le_of_surjective` as new inventory items.

**The single most important improvement**: The boss (L05) must be redesigned. It currently does not integrate the world's content -- it is a near-copy of L01 with trivially different arithmetic. An example world lives or dies by whether its levels make abstract concepts concrete, and the boss is the place where concretization reaches its peak. The current boss is the weakest level in the world precisely because it repeats rather than integrates. Suggestions 1 and 2 together would transform this from a world that *talks about* counting functions into one where the learner *works with* counting functions at multiple levels of abstraction.
