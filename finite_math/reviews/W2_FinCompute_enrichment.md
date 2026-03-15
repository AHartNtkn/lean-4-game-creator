# Enrichment Review: W2 FinCompute ("Computing with Fin")

Reviewer: lean4game-enrichment-reviewer
Date: 2026-03-14
World files: L01_FinCases through L08_Boss (8 levels)
Context: W1 (FinIntro) with 13 levels, course plan at PLAN.md

---

## Ranked suggestions

### 1. L07 claims to teach "building a function on Fin n" (V19) but actually proves a universally quantified inequality -- the plan's promise is unmet

**What**: The plan for W2 level 7 says: "**Building a function on `Fin n`**: Define a function `Fin 3 -> Nat` by cases | Recursive/inductive construction; V19". The actual L07 proves `forall i : Fin 3, 2 * i.val + 1 < 10`, which is a rehash of L01-L02's pattern (fin_cases + omega). No function is defined, no recursive construction is taught, and V19 (recursive/inductive construction over Fin n) is not covered at all.

**Why**: V19 is a genuinely new proof move -- defining a function on `Fin n` by splitting into cases and giving a value for each. This is different from *proving a proposition* by fin_cases; it is *constructing data* by cases. The learner needs this skill in W3_ex (defining a function on Fin 3), in W11 (Fintype instances for function types), and extensively in W22-W23 (permutations and matrices as functions). Without a level that actually teaches function definition by cases on Fin, the world has a gap in its coverage. The current L07 is essentially L01 with a different arithmetic expression -- it introduces no new concept, proof move, or tactic.

**Where**: Rewrite L07 entirely. The statement should involve constructing or reasoning about a function `Fin n -> Nat` or `Fin n -> Fin m` defined by case analysis. For example: define `f : Fin 3 -> Nat` by `f 0 = 1, f 1 = 4, f 2 = 9` (the squares plus 1), then prove `f (1 : Fin 3) = 4`. Or prove that a given function definition is correct on each input. The proof would use `fin_cases` not to close arithmetic goals but to reduce a function application to its case-specific definition. Alternatively, a level proving that a function defined by `fun i : Fin 3 => if i = 0 then 1 else if i = 1 then 4 else 9` satisfies `f 1 = 4` would teach `if`/`then`/`else` in Lean, which connects to W8 (Finset.filter with decidable predicates).

**Effort**: High (rewrite one level).

**Recommend**: Yes.

---

### 2. Modular arithmetic (L06) is a single computation level with no follow-up -- subtraction and the wrap-around structure are untested

**What**: L06 proves `(3 : Fin 5) + (4 : Fin 5) = (2 : Fin 5)` using `decide`. The introduction mentions subtraction (`1 - 3 = 3` in Fin 5) and that Fin n forms a ring, but neither fact is tested. The learner sees one addition example and moves on.

**Why**: Modular arithmetic on `Fin n` is coverage item M4, which the plan marks as introduced (I) in this level. But a single `decide` proof does not teach modular arithmetic -- it teaches that `decide` can verify concrete equalities. The learner never confronts the wrapping behavior, never sees subtraction, and never encounters the zero element. More importantly, the "ring" claim in the conclusion ("`Fin n` with `n >= 1` forms a commutative ring") is a significant mathematical statement that is neither proved nor concretized. At minimum, a level demonstrating subtraction wrapping (`(1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5)`) would ground the claim. Better still, a level showing that `(a + b) - b = a` holds in `Fin 5` for a specific `a, b` would preview the ring structure.

The wrap-around behavior is precisely what makes `Fin n` arithmetic surprising and pedagogically rich. A learner who sees only `3 + 4 = 2` might think "oh, it reduces mod n" but not internalize *subtraction* wrapping, which is less intuitive. This is the kind of concrete example that, once pointed out, feels obvious to include.

**Where**: Add a level after L06 (or split L06 into two levels). New level: prove `(1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5)` or prove both an addition and a subtraction fact about `Fin 7` arithmetic. The proof is still `decide`, so the tactic burden is zero -- the novelty is the mathematical content (subtraction wrapping).

**Effort**: High (new level).

**Recommend**: Yes.

---

### 3. The "tactic selection" lesson (L04) is too soft -- both approaches solve the goal identically, so the learner cannot feel the difference

**What**: L04 is titled "decide vs fin_cases" and presents a goal (`forall i : Fin 3, i.val = 0 or i.val >= 1`) solvable by both `decide` and `fin_cases i <;> omega`. The introduction says "try both approaches and feel the difference," but both approaches work in one line, and the proof does not require `left`/`right` as the introduction suggests (because `omega` handles disjunctions). The learner has no reason to prefer one over the other.

**Why**: The stated pedagogical goal is tactic selection -- knowing when to reach for `decide` vs `fin_cases`. But L04 does not achieve this because the goal is not discriminating. A genuinely discriminating level would present a goal where one tactic works and the other does not (or works poorly). For example: a goal involving a non-decidable component (like `Exists` with a function that is not computable) where `decide` fails and `fin_cases` is needed; or a goal where `decide` is dramatically simpler than `fin_cases` because the case analysis would require lemma applications, not just arithmetic. The current L04 teaches "both work, take your pick," which is not a useful heuristic.

**Where**: Rewrite L04's statement. One approach: make the goal require a lemma application or rewriting in at least one case after `fin_cases`, so that `decide` is strictly simpler for this goal. Then make L04b (or a follow-up hint) show a goal where `decide` is too slow or fails, requiring `fin_cases`. The plan says "Two similar goals, one solved by `decide`, the other needing `fin_cases` + reasoning." The world delivers only one goal, not two. Consider making L04 a two-part level with two statements (if the game engine supports it), or splitting into two levels.

**Effort**: Medium (rewrite one level).

**Recommend**: Yes.

---

### 4. No level demonstrates `decide` failing or being slow -- the limitation is mentioned but never experienced

**What**: L03's conclusion warns that `decide` "can be slow or fail on large types." L04's conclusion repeats this. But the learner never sees `decide` struggle. There is no level where the learner attempts `decide`, finds it slow or unhelpful, and must fall back to `fin_cases` or manual reasoning.

**Why**: Tactic limitations are best learned by experiencing them, not by reading warnings. A level with a statement about `Fin 100` or `Fin 50` where `decide` times out (or the game engine rejects it for being too slow) and the learner must use `i.isLt` + `omega` instead would be a powerful teaching moment. It would also reinforce the W1 technique (which used `i.isLt` for general `Fin n` reasoning) as the correct approach for larger types, cementing the three-strategy hierarchy: `decide` for tiny concrete types, `fin_cases` for small concrete types, `i.isLt` + arithmetic for general `n`. The plan's conclusion for L04 states this hierarchy but never tests it.

Alternatively, rather than a timeout (which may be fragile), a level could present a goal that is *not decidable* -- e.g., involving a universally quantified hypothesis over an infinite type as a premise -- where `decide` simply does not apply. This teaches the *conceptual* limitation, not just the performance one.

**Where**: New level after L04, or fold into the L04 rewrite (suggestion 3). Alternately, this could be placed before the boss as L07 (after the function level), showing that for `Fin 50`, `fin_cases` is impractical and `i.isLt` + `omega` is the way.

**Effort**: High (new level).

**Recommend**: Consider. The three-strategy hierarchy is clearly articulated in prose, and W1 already taught the general strategy. An experiential level would be ideal but may not be strictly necessary if the prose is clear enough. However, it would make the tactic selection lesson genuinely stick.

---

### 5. The boss (L08) does not require `decide` -- one of the three new tactics is untested in the integration level

**What**: The boss proves `forall i : Fin 5, 0 < i.val ^ 2 + 1 and i.val ^ 2 + 1 < 20` using `fin_cases i <;> norm_num`. The tactic `decide` is not needed and not used. The boss tests `fin_cases` and `norm_num` but not `decide`.

**Why**: The world introduces three new tactics: `fin_cases`, `decide`, and `norm_num`. A good boss should require or meaningfully benefit from at least two, ideally all three. The current boss is solvable without `decide`, making `decide` a tactic that was introduced, practiced in two levels (L03 and L06), but never required for any level that also requires other skills. A boss that combines `decide` with `fin_cases` or `norm_num` -- for example, a conjunction where one conjunct needs `decide` (a decidable equality or ordering statement) and the other needs `fin_cases` + `norm_num` -- would give `decide` a role in the integration.

**Where**: Modify L08's statement to include a conjunct or a step that benefits from `decide`. For example: prove both a property of a function on `Fin 5` (requiring `fin_cases` + `norm_num`) AND a concrete equality between two `Fin 5` elements (best solved by `decide`). Or make the boss require two proof steps where the learner chooses different tactics for each.

**Effort**: Medium (modify one level).

**Recommend**: Yes.

---

### 6. No counterexample or "what if" level -- modular arithmetic has natural misconception opportunities that are ignored

**What**: The world does not include any level where the learner confronts a false belief about `Fin n` arithmetic. For example, the learner might believe that addition on `Fin n` matches natural number addition (it does not, because of wrapping), or that `Fin n` has a multiplicative inverse for every nonzero element (it does not, unless `n` is prime), or that `a + b = b + a` needs proof (it is automatic from the ring structure).

**Why**: Misconception levels are high-value pedagogical moments. The plan lists C5 and C6 as the misconceptions for W2, both about indexing (already addressed in W1). But M4 (modular arithmetic) introduces its own misconception: that `Fin n` arithmetic is "just natural number arithmetic." A level that asks the learner to prove (or disprove) something like `(2 : Fin 4) + (3 : Fin 4) = (5 : Fin 4)` -- which is FALSE because `5` in `Fin 4` wraps to `1` -- would make the wrapping visceral. The learner would need to understand that `(5 : Fin 4)` is coerced to `(1 : Fin 4)`, so the equality *does* hold but is surprising. Or even better: prove `(2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4)` (since `6 mod 4 = 2`), which challenges the naive expectation that `2 * 3 = 6`.

**Where**: Add a level after L06 that presents a "surprising" modular arithmetic fact, or modify L06 to have two parts (the expected case and the surprising case).

**Effort**: Medium (modify one level or add one).

**Recommend**: Consider. This overlaps with suggestion 2 (subtraction wrapping) but focuses on a different aspect (multiplication). Either suggestion would improve the modular arithmetic coverage; both together would be ideal but might make the world too long. If only one is implemented, suggestion 2 (subtraction) is higher priority because subtraction wrapping is less intuitive than multiplication wrapping.

---

### 7. The semicolon combinator `<;>` is taught in L01 but never named as a general tool

**What**: L01's conclusion explains that `fin_cases i <;> omega` uses the semicolon to "apply omega to every goal produced by fin_cases i" and calls it a "combinator." But the conclusion does not explain that `<;>` works with any pair of tactics, not just `fin_cases` and `omega`. Every subsequent level uses `<;>` without comment.

**Why**: The `<;>` combinator is a Lean tactic-mode feature that the learner will use throughout the course (e.g., `ext <;> simp`, `constructor <;> intro h`). If it is only understood as "the thing that goes between fin_cases and omega," the learner will not recognize it as a general tool. A sentence in L01's conclusion -- "The semicolon `<;>` applies the following tactic to *every* goal created by the preceding tactic. It works with any pair of tactics, not just `fin_cases` and `omega`" -- would generalize the lesson appropriately.

**Where**: L01 conclusion.

**Effort**: Low (one sentence expansion).

**Recommend**: Yes.

---

### 8. Cross-world foreshadowing: `decide` will return for Finset membership and decidable predicates

**What**: The `decide` tactic is introduced here for `Fin n` propositions but will be used again in W5 (DecidableEq for Finsets), W6 (membership in concrete finsets), and W8 (filter with decidable predicates). The conclusion of L03 does not mention these future uses.

**Why**: `decide` is a tactic whose scope extends far beyond `Fin n`. By mentioning in L03's conclusion that "decidable propositions will appear again when you work with finsets -- membership in a concrete finset is decidable, and filtering requires a decidable predicate," the world seeds vocabulary (`decidable`, `DecidableEq`) that will be essential in W5-W8. This costs a single sentence and prevents the learner from pigeonholing `decide` as "a Fin thing."

**Where**: L03 conclusion, add 1-2 sentences.

**Effort**: Low (sentence addition).

**Recommend**: Yes.

---

### 9. `norm_num` is introduced with a goal that `omega` also solves -- the learner has no reason to learn a new tactic

**What**: L05 proves `(2 : Fin 7).val * (3 : Fin 7).val = 6`. The introduction admits that "omega would also work here since the goal is linear once simplified." The learner has no reason to learn `norm_num` when `omega` already works.

**Why**: A tactic should be introduced with a goal where it is *necessary*, not merely optional. If `omega` solves the goal, the learner will (correctly) ask "why do I need norm_num?" The introduction says `norm_num` is "the standard choice for numeric evaluation," but standard practice is not a compelling reason for a learner to adopt a new tool. A goal involving `^` (powers), factorials, or other non-linear operations that `omega` cannot handle would properly motivate `norm_num`. The boss level (L08) actually provides such a goal (`i.val ^ 2 + 1`) -- but by the time the learner reaches the boss, they have not practiced `norm_num` on a goal that requires it.

**Where**: Change L05's statement to one that `omega` cannot solve. For example: `(3 : Fin 10).val ^ 2 = 9` or `(2 : Fin 8).val ^ 3 + 1 = 9`. These involve powers, which `omega` cannot handle, making `norm_num` genuinely necessary.

**Effort**: Medium (modify one level's statement).

**Recommend**: Yes.

---

### 10. No transfer moment in the world -- the plan calls for a transfer on the boss but the world has none

**What**: The plan marks V18 (R) on the boss: "`have` should be reviewed as a proof-structuring tool." The boss conclusion includes a transfer paragraph mapping `fin_cases` to "checking each element" in paper proofs, but this is passive reading. There is no active transfer moment anywhere in the world -- no level asks the learner to connect the exhaustive-case-analysis proof pattern to how they would write it on paper.

**Why**: W1 was enriched to include genuine transfer connections (e.g., "This is exactly what a mathematician means by..."). W2 should maintain the same standard. The exhaustive-verification pattern (`fin_cases` followed by a closer) is one of the most transferable proof moves in the course -- it corresponds directly to "we check each case" in paper proofs. A transfer sentence in L07's conclusion (where the pattern is applied to functions) would be natural: "This is exactly what a mathematician means by 'we verify the claim for each element of the domain.'" -- and indeed, the current L07 already has this sentence, which is good. But the boss conclusion could be stronger: instead of just listing the tactic summary table, it could include a worked transfer example showing the paper-proof version of the boss statement.

**Where**: L08 conclusion (expand the transfer paragraph).

**Effort**: Low (expand conclusion text).

**Recommend**: Consider. L07 already has a transfer sentence. The boss conclusion has a brief transfer too. This is adequate but not ideal. Expanding the boss conclusion is a modest improvement.

---

### 11. The world has no introduction -- the learner enters without context on what "computing" means

**What**: The world file (`FinCompute.lean`) has no world-level introduction or conclusion text. The learner sees the world name "FinCompute" and the first level title "Introducing fin_cases" but has no world-level context about what the world will teach, what prerequisites it assumes, or what the goal is.

**Why**: W1 (FinIntro) presumably sets up the transition to W2 in its boss conclusion. But if the game engine supports world-level introductions (as most Lean4Game implementations do), a 2-3 sentence introduction would help: "You know what `Fin n` is. Now you will learn to *compute* with it -- verifying properties by checking every element, evaluating numeric expressions, and working with modular arithmetic." This orients the learner and makes the world's promise explicit.

**Where**: Add world-level introduction text to `FinCompute.lean` or to L01's introduction as a preamble.

**Effort**: Low (a few sentences).

**Recommend**: Consider. The L01 introduction already provides context. A world-level intro would be a nice-to-have but is not critical if the game engine does not prominently display it.

---

### 12. Unnamed strategy: the "fin_cases + closer" pattern is used 5 times but never given a name

**What**: The pattern `intro i; fin_cases i <;> closer_tactic` appears in L01, L02, L04, L07, and L08. The conclusion of L01 calls `<;>` a "combinator" and L08's table describes the pattern as "each-case verification on Fin n," but the pattern itself is never given a memorable name like "exhaustive verification" or "case-by-case check."

**Why**: When a proof pattern is used repeatedly, naming it helps the learner recognize it as a strategy rather than a sequence of unrelated tactic calls. The W1 enrichment review (suggestion 6, about the boss) already pushed for more integration of proof moves. In W2, the exhaustive verification strategy is the central proof move, and naming it explicitly -- perhaps as "the exhaustive check" or "case-by-case verification" -- would help the learner articulate what they are doing in paper proofs. The plan lists V2 (case splitting/exhaustion on Fin n) as the proof move for this world; giving it a human-readable name makes it transferable.

**Where**: L01 conclusion or L02 conclusion, where the pattern is first solidified.

**Effort**: Low (naming in prose).

**Recommend**: Yes.

---

## Overall impression

**What the world does well**: The world has a clear pedagogical arc from introducing `fin_cases` (L01) to combining tactics (L08). Each of the three new tactics (`fin_cases`, `decide`, `norm_num`) gets its own dedicated level. The introductions are well-written, with accurate mathematical content and genuine comparisons between tactics. The L04 and L08 conclusions provide useful tactic-selection heuristics. The prose explains not just how each tactic works but when to use it, building the learner's judgment rather than just their muscle memory. The L06 modular arithmetic level is a welcome mathematical interlude that connects `Fin n` to number theory.

**The single most important improvement**: Rewrite L07 to actually teach function definition by cases on `Fin n` (suggestion 1). The current L07 is a clone of L01-L02 with different numbers, introducing no new concept and leaving the plan's V19 coverage item (recursive/inductive construction) entirely unaddressed. This is the most significant gap because it is a *missing proof move* -- the learner enters W3_ex expecting to define functions on `Fin 3` but has never seen the pattern for doing so. Secondary to this, the modular arithmetic coverage (suggestion 2) should be deepened with at least one additional computation showing subtraction wrapping, and `norm_num` (suggestion 9) should be introduced with a goal that genuinely requires it rather than one where `omega` suffices.
