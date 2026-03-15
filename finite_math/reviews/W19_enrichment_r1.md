# W19 BinomialTheorem -- Enrichment Review R1

## Ranked suggestions

### 1. The plan calls for proving the binomial theorem by induction (L03-L06), but the world instead uses `exact add_pow` everywhere -- the inductive structure is entirely absent

**What**: The plan explicitly designs levels 3-6 as base case, inductive step part 1, inductive step part 2, and assembly of the full proof. The actual world collapses all of that into repeated one-line `exact add_pow ...` calls. The learner never sees induction, never uses Pascal's rule, never performs the distributive step. The entire proof-move layer for M29 (understanding *why* the binomial theorem holds) is missing.

**Why**: This is the most serious gap. The world's promise says "The learner can prove the binomial theorem," but the learner never proves it -- they only invoke a library lemma. Levels L01, L03, L04, and L09 are all structurally identical (`exact add_pow ...` with different arguments). Four levels that teach the same single proof move produce no learning progression. The plan's design -- building the inductive proof across four levels -- would have been the pedagogical centerpiece of this world. Without it, the world has no mathematical depth; it is a sequence of library-call exercises.

**Where**: L01, L03, L04, L09 need a complete redesign. Levels 3-6 should follow the plan's inductive structure (base case, expand, recombine via Pascal's rule, assemble). L01 can stay as a concrete verification, but L09's "transfer" level is redundant with L01/L03 (all three are `exact add_pow`).

**Effort**: High (restructuring 4-6 levels)

**Recommend**: Yes

---

### 2. `push_cast` is introduced in L02 on an isolated arithmetic identity, then never used again in any subsequent level

**What**: L02 teaches `push_cast` on `(n * (n + 1) : Z) = n * (n + 1)`, but no later level in the world requires the learner to use `push_cast`. The boss (L10) works in Z with casts, but the proof is `have h := add_pow ...` followed by `rw` and `exact` -- no `push_cast` needed. The tactic is introduced and then immediately abandoned.

**Why**: The plan marks L15 (`push_cast`) as introduced in this world, and the world promise specifically mentions "can work with `push_cast`/`Nat.cast` when sums land in other types." A tactic that appears once in an isolated exercise and is never reinforced is not learned. At least one subsequent level should require `push_cast` as part of a real proof, not as a standalone drill.

**Where**: L02 (needs a follow-up), and at least one of L08/L10 should be restructured so `push_cast` is a necessary step.

**Effort**: Medium (modifying 1-2 levels to integrate `push_cast` into a genuine proof)

**Recommend**: Yes

---

### 3. Missing: symmetry identity for binomial coefficients (`choose n k = choose n (n-k)`) as derivable from the binomial theorem

**What**: The plan lists binomial symmetry as a W18 topic, but there is a beautiful and non-obvious derivation of `choose n k = choose n (n-k)` from the binomial theorem itself (compare the expansion of `(1 + x)^n` with `(x + 1)^n` and equate coefficients, or use commutativity of addition). The world's L07 conclusion mentions the "sum of squares" identity as a Vandermonde corollary but never shows it. A level deriving symmetry from the binomial theorem would connect W18 and W19 beautifully.

**Why**: The plan lists M30 (symmetry) as covered in W18 and the world doesn't attempt it. But W19 is the natural place to show that symmetry is a *consequence* of the binomial theorem -- this is a derivable result being treated as an axiom. The enrichment skill specifically flags "derivable results presented as axioms" as the most important category.

**Where**: New level between L05 (row sum) and L06 (Vandermonde), or incorporated into the restructured L03-L06 sequence.

**Effort**: Medium (new level)

**Recommend**: Consider

---

### 4. No level requires multi-step reasoning -- every level is solvable in 1-2 lines

**What**: L01: `exact add_pow 2 3 2`. L02: `push_cast; ring`. L03: `exact add_pow x y n`. L04: `exact add_pow 1 1 n`. L05: `exact Nat.sum_range_choose n`. L06: `exact Nat.add_choose_eq m n k`. L07: `exact Nat.add_choose_eq 2 3 2`. L08: `exact Int.alternating_sum_range_choose_of_ne hn`. L09: `exact add_pow a b n`. The boss (L10) is the only level with more than 2 steps, and even there the steps are small (each is a `have` or `rw`).

**Why**: A world where 9 of 10 levels are single-tactic solutions teaches "library lookup," not mathematics. The learner never struggles, never combines tools, never makes a proof-move decision. The proof-move layer is nearly empty. Even accounting for the fact that some levels are intentionally simple (concrete verifications, library introductions), the overall profile is too flat. The boss is the right difficulty, but there should be at least 2-3 levels in the middle that require 3+ steps.

**Where**: Systemic across L03-L09. The restructured inductive-proof levels (suggestion 1) would fix this for L03-L06. L05 and L08 could be restructured to derive the identity from the binomial theorem (as shown in L04's conclusion) rather than just invoking a library lemma.

**Effort**: High (tied to suggestion 1)

**Recommend**: Yes

---

### 5. L04 derives the row sum from the binomial theorem, but L05 just invokes `Nat.sum_range_choose` -- the derivation gap is the lesson

**What**: L04 shows that setting x=1, y=1 gives the row sum. Then L05 asks the learner to prove the same identity, but accepts `exact Nat.sum_range_choose n` -- a library call that has nothing to do with the derivation from L04. The natural level would have the learner *complete* the derivation: start with `add_pow 1 1 n`, simplify `1^k * 1^(n-k)` to `1`, and conclude `2^n = sum choose n k`.

**Why**: The conclusion of L04 explicitly says "since 1^k = 1, each term simplifies to just choose n k." But the learner never does this simplification! That *is* the interesting step. L05 should be a level where the learner takes the output of L04 and simplifies it, not a redundant library call.

**Where**: L05 should be rewritten to require simplifying the L04 output into the clean row-sum identity, using `one_pow`, `one_mul`, and `Finset.sum_congr` (or similar).

**Effort**: Medium (rewriting one level)

**Recommend**: Yes

---

### 6. L08 (alternating sum) is a library call, but the derivation from the binomial theorem is the whole point

**What**: Like L05, L08 asks the learner to prove the alternating sum identity but accepts `exact Int.alternating_sum_range_choose_of_ne hn`. The learner never performs the specialization x=1, y=-1 that the introduction describes. The conclusion even describes two proofs (algebraic and combinatorial) but the learner used neither.

**Why**: The plan says this level teaches "sign manipulation in sums." But no sign manipulation occurs. The level should have the learner apply `add_pow 1 (-1) n`, simplify `(1 + (-1))^n = 0^n = 0` (using `add_right_neg` or `ring`, then `zero_pow`), and then relate the resulting sum to the target. This would give `push_cast` a second appearance (the sum involves casts) and create genuine proof-move content.

**Where**: L08 should be restructured as a multi-step derivation.

**Effort**: Medium (rewriting one level)

**Recommend**: Yes

---

### 7. The boss is well-structured but gives away the entire strategy in the introduction

**What**: L10's introduction tells the learner exactly what to substitute (x=-1, y=2), writes out the full proof plan in 4 numbered steps, and even shows the concrete check for n=3. The hints then repeat the exact same steps. There is no moment where the learner must figure out what to do.

**Why**: A boss level should test whether the learner can *choose* the right approach, not just execute it. The introduction should set up the problem ("prove this identity") and perhaps remind the learner that specialization is the key technique. The *choice* of x=-1, y=2 is the interesting proof move and should come from the learner (or from the first hint, not the introduction).

**Where**: L10 introduction should be trimmed. Move the strategy to a hidden hint. Let the first visible hint say something like "Think about what values to substitute into the binomial theorem."

**Effort**: Low (editing text)

**Recommend**: Yes

---

### 8. `exact_mod_cast` is mentioned in L02's conclusion but never declared as NewTactic and never used

**What**: The L02 conclusion says "Another useful tactic: `exact_mod_cast`. Sometimes you already have a proof `h : a = b` in N, and need `a = b` in Z. The tactic `exact_mod_cast h` handles this automatically." But this tactic never appears again, has no `TacticDoc`, and is not in `NewTactic`.

**Why**: Either teach it properly (add a level or exercise using it) or remove the mention. A tactic mentioned in passing but never used creates the impression of being important without providing practice. Since this world already has a `push_cast` problem (suggestion 2), a cleaner approach might be to add a level where the learner must use `exact_mod_cast` to handle a cast that `push_cast` alone doesn't solve, providing both reinforcement and a new tool.

**Where**: L02 conclusion, potentially a new level.

**Effort**: Low (remove mention) or Medium (add a level using it)

**Recommend**: Consider

---

### 9. No "what if?" or misconception content -- the world never shows where hypotheses matter

**What**: L08 requires `n != 0` for the alternating sum identity. The world never asks: what happens when n = 0? (The sum is 1, not 0.) This is a natural misconception level -- the learner might assume the alternating sum is always 0. Similarly, the binomial theorem requires commutativity of the ring, but this is never mentioned as a hypothesis.

**Why**: Showing *why* `n != 0` is needed in L08 would cost a single sentence or a 1-step exercise (compute the alternating sum for n=0). It makes the hypothesis feel necessary rather than arbitrary. This is a pedagogical opportunity from category 4 of the enrichment skill.

**Where**: L08 (add a remark or a small exercise before the main statement)

**Effort**: Low (adding text to L08's introduction or conclusion)

**Recommend**: Consider

---

### 10. The Vandermonde conclusion (L07) mentions "sum of squares of a row" identity but never proves or even states it in Lean

**What**: L07's conclusion says "Setting m = n and k = n gives C(2n, n) = sum C(n,j)^2" but this is left as a remark. This is a beautiful and well-known identity that could be a short level (specialize Vandermonde with m=n, k=n).

**Why**: This is exactly the kind of "derivable result" the enrichment reviewer exists to catch. The identity is mentioned, so the world author clearly knows about it, but the learner never proves it. A level deriving it from Vandermonde would reinforce the "specialization" proof move and give a second use of `Nat.add_choose_eq`.

**Where**: New level after L07, or incorporated into L07 as a second part.

**Effort**: Medium (new level or extended level)

**Recommend**: Consider

---

### 11. No historical or motivational context for Vandermonde's identity

**What**: L06 and L07 present Vandermonde's identity with a combinatorial interpretation ("committee" counting argument in L06's conclusion) but no historical context. Vandermonde's identity has a rich history -- it was known to Chu Shih-Chieh in 1303, predating Vandermonde by centuries. It is sometimes called the Chu-Vandermonde identity.

**Why**: A single sentence of historical context ("This identity was known in China as early as 1303, long before Vandermonde rediscovered it in 1772") costs nothing and adds texture. The enrichment skill's category 4 mentions historical context as a pedagogical opportunity.

**Where**: L06 introduction or conclusion.

**Effort**: Low (one sentence)

**Recommend**: Consider

---

## Overall impression

The world has a strong thematic arc -- the binomial theorem as a "generating function" for identities, where different substitutions yield different results (row sum from x=y=1, alternating sum from x=1,y=-1, boss from x=-1,y=2). The L10 boss is the right capstone, and the Vandermonde interlude (L06-L07) provides variety. The conclusions are consistently well-written, with transfer moments and clean mathematical summaries.

However, the single most important improvement is **suggestion 1**: the world's level ladder is almost entirely composed of one-line library calls. The plan designed levels 3-6 as a genuine inductive proof of the binomial theorem -- base case, distributive expansion, Pascal recombination, and assembly -- but the actual world replaces all of that with `exact add_pow`. This eliminates the proof-move layer almost entirely. Nine of ten levels are solvable by a single `exact` or two-tactic sequence, and the learner never constructs a real proof until the boss. Restructuring the core levels (L03-L06) to follow the plan's inductive design, and restructuring L05 and L08 to derive identities from the binomial theorem rather than invoking library lemmas, would transform this from a library-tour into a genuine learning experience.
