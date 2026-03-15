# Enrichment Review (Third Pass): W2 FinCompute ("Computing with Fin")

Reviewer: lean4game-enrichment-reviewer
Date: 2026-03-14
World files: L01_FinCases through L11_Boss (11 levels)
Context: W1 (FinIntro, 13 levels), course plan at PLAN.md, prior enrichment reviews (r1 and r2), prior playtest audits (r1 and r2)

---

## Status of second-review suggestions

| # | Second-review suggestion | Status |
|---|-------------------------|--------|
| 1 | L08 teaches formula evaluation, not case-defined function construction (V19 partial) | **Unchanged.** L08 still evaluates `(0 : Fin 3).val ^ 2 + 1 + ... = 8` via `norm_num`. No `match`, `if`/`then`/`else`, or case-defined function appears. The gap is acknowledged as narrow (concept taught, syntax not). |
| 2 | L10 does not genuinely require different closers per case | **Unchanged.** L10's statement `∀ i : Fin 3, i.val ^ 2 ≤ 4 ∧ i.val + 1 ≤ 3` is closed by `fin_cases i <;> (constructor <;> norm_num)`. `norm_num` handles both the power and the linear part in every case. The learner never needs to write distinct per-case tactics. |
| 3 | Modular arithmetic block is pure `decide` -- no `Fin.val`/`Fin.ext` connection | **Unchanged.** L07 and L09 are both closed by `decide`. The learner never sees the computation in terms of `.val` or `% n`. |
| 4 | No world-level introduction or conclusion | **Unchanged.** `FinCompute.lean` contains only imports. |
| 5 | L09 should include the zero-divisor conjunct `2 * 2 = 0` | **Addressed.** L09 now proves the conjunction `((2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4)) ∧ ((2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4))`. The zero-divisor fact is now interactive, not just prose. |
| 6 | Tactic trio table inconsistencies across L05, L10, L11 | **Unchanged.** The tables still exist in three slightly different forms. |

Additionally, the playtest audit (r2) identified P0 exploitability defects (`native_decide` bypass, `decide` on boss). These have been fixed:
- `native_decide` is now disabled on all 11 levels.
- `decide` is disabled on the boss (L11) and on all levels except L03, L07, L09.
- The boss statement has been changed from a modular-arithmetic-plus-universal to `(3 ^ 2 + 4 ^ 2 = 25) ∧ (∀ i : Fin 5, i.val ^ 2 < 25)`, which is fully closable by `constructor; norm_num; intro i; fin_cases i <;> norm_num`.

---

## Ranked suggestions (third pass)

### 1. L10 still does not achieve its stated pedagogical goal -- "different closers for different cases" never actually occurs

**What**: L10's introduction promises to teach per-case tactic selection: "what if different cases need different tactics?" But the statement `∀ i : Fin 3, i.val ^ 2 ≤ 4 ∧ i.val + 1 ≤ 3` is uniformly closable by `constructor <;> norm_num` in every case. `norm_num` handles both the power inequality and the linear inequality. The learner never writes the `·` case bullets with genuinely different closers.

**Why**: This is the world's weakest pedagogical link. The level title is "Choosing the right closer," the introduction discusses the problem of cases needing different tactics, but the implementation does not create that situation. A learner who reaches L10 and solves it with `fin_cases i <;> (constructor <;> norm_num)` has not practiced the skill the level claims to teach. This was flagged in the second review (suggestion 2) and remains unaddressed.

To genuinely teach this skill, the statement should force the learner to handle at least one case differently. For example, a goal where one case involves a hypothesis that requires `simp` or `rfl` while another involves `norm_num`, or a goal where the conjunction's two parts require `omega` and `norm_num` respectively and `norm_num` does not close the `omega` part. Even simpler: include a case that requires `Nat.zero_le` or `Nat.le_refl` (which `norm_num` may not fire on) alongside a case requiring `norm_num` for a power.

Alternatively, if the real lesson is "use `constructor <;> norm_num` as a compound closer" (which is what the learner actually learns), rename the level and reframe the introduction to match what the level teaches. Honesty in framing is better than aspirational framing that the content does not deliver.

**Where**: Redesign L10's statement, or reframe its introduction and title to match the actual lesson.

**Effort**: Medium (redesign statement) or low (reframe prose).

**Recommend**: Yes. The mismatch between promise and delivery is the world's most noticeable remaining flaw.

---

### 2. The boss no longer tests `decide` -- the tactic trio is reduced to a tactic duo in the integration level

**What**: The boss (L11) proves `(3 ^ 2 + 4 ^ 2 = 25) ∧ (∀ i : Fin 5, i.val ^ 2 < 25)` with `constructor; norm_num; intro i; fin_cases i <;> norm_num`. Both parts use `norm_num`. The tactic `decide` -- one of the three new tactics introduced in this world -- plays no role in the boss. This appears to be a consequence of fixing the P0 exploitability defect: `decide` was disabled on the boss to prevent one-shot bypass, and the statement was redesigned to avoid needing `decide` at all.

**Why**: The first enrichment review (suggestion 5) flagged the original boss for not requiring `decide`. The re-authoring addressed this by making the boss's first conjunct a modular arithmetic equality best solved by `decide`. The second playtest review praised this integration. But the current boss has reverted: the modular arithmetic conjunct is gone, replaced by a pure numeric identity `3 ^ 2 + 4 ^ 2 = 25` that `norm_num` handles.

The result is that `decide` is introduced in L03, practiced in L07 and L09, and then never needed again. It is not tested in the boss. The boss tests `fin_cases`, `norm_num`, and `constructor` -- but not `decide`. This means `decide` has no graduation (G) moment in W2. The coverage status should be L3(I), L3(S via L07/L09) but no L3(G).

This is not blocking -- `decide` will be heavily used in later worlds (finset membership, decidable predicates). But within W2, the tactic trio promise is partially unfulfilled.

A possible fix: make the boss a three-part conjunction where the third part is a decidable equality like `(2 : Fin 5) + (3 : Fin 5) = (0 : Fin 5)`. Keep `decide` disabled, but add a `Branch` that accepts `norm_num` for this part. Alternatively, add a `Branch` on L07 or L09 that accepts `norm_num` as an alternative to `decide`, and consider the modular arithmetic levels as the graduation moment for `decide`.

**Where**: L11 (boss) -- add a third conjunct, or accept that `decide` graduates in L09 rather than in the boss.

**Effort**: Medium (add a conjunct to the boss) or none (accept the current design and update coverage tracking).

**Recommend**: Consider. The current boss is clean and coherent as a `fin_cases + norm_num` integration. Adding a `decide` component would improve coverage completeness but risks making the boss a three-part gauntlet rather than a two-part integration. If the boss stays as-is, the world conclusion should not claim `decide` is "integrated" in the boss.

---

### 3. L10's `simp_all` mention is still present -- an untaught tactic is named in the introduction

**What**: L10's introduction says: "Or try `<;> simp_all` or `<;> (first | omega | norm_num)` --- but explicit case handling is clearest." Neither `simp_all` nor `first` has been taught. The playtest audit (r2) flagged this as P3-1 and recommended removal or disabling.

**Why**: A curious learner who reads this sentence and tries `simp_all` may find that it works (since `simp_all` is not disabled on L10). If it closes the goal, the learner bypasses both `fin_cases` and the per-case handling lesson entirely. This is a minor exploitability leak. More importantly, naming untaught tactics in introductions can cause confusion: the learner may wonder whether they should have learned `simp_all` somewhere and feel they missed something.

**Where**: L10 introduction, line 33.

**Effort**: Low (delete or rephrase one sentence).

**Recommend**: Yes. This is a two-minute fix that eliminates a minor exploitability leak and an unnecessary source of confusion.

---

### 4. The tactic selection summary tables across L04, L05, L10, and L11 use inconsistent framing

**What**: Four levels include tactic comparison tables with slightly different structures:
- L04: three-row table comparing `decide`, `fin_cases + closer`, `i.isLt + omega` on Scope and Control.
- L05: three-row table comparing `omega`, `norm_num`, `decide` on "Goal type" and "Best tactic."
- L10: a five-item bullet list (omega, norm_num, decide, constructor, manual handling).
- L11: two tables -- a four-row "What you learned" table and a three-row "tactic selection hierarchy" table.

The framing shifts between tables: L04 frames by "Strategy" and "Scope." L05 frames by "Goal type." L10 uses a flat list. L11 uses two different framings in two tables. The descriptions also evolve: L04 says `decide` works on "small concrete `n`, fully decidable goals"; L05 says it works on "decidable propositions on finite types"; L11 says it works on "concrete equality/inequality on small `Fin n`."

**Why**: Progressive refinement of summary tables is good pedagogy (spaced retrieval with increasing sophistication). But the inconsistency in column headers and tactic descriptions may undermine the learner's sense of having a stable mental model. When the same tactic is described three different ways across four levels, the learner may wonder which description is "right."

The fix is not to make all tables identical (that would be boring and miss the progressive-refinement opportunity), but to use a consistent framing dimension (e.g., always "Situation -> Best tactic") and consistent tactic descriptions, while adding new rows as new tactics are taught.

**Where**: L04, L05, L10, L11 conclusions.

**Effort**: Low (text harmonization across four conclusions).

**Recommend**: Consider. This is polish. The current inconsistencies are unlikely to confuse most learners, and some variability in presentation may actually help by forcing the learner to re-process the information rather than just scanning a familiar table. But if the tables are meant to serve as reference material (which the boss's version clearly is), consistent framing would make them more useful.

---

### 5. L08 title and introduction still overpromise -- "Defining and Verifying Functions" when the learner only evaluates a formula

**What**: L08's title is "Verifying a function on Fin by cases" and the introduction says "Defining and Verifying Functions on `Fin n`." But the statement is `(0 : Fin 3).val ^ 2 + 1 + ... = 8`, which is a concrete numeric expression evaluated by `norm_num`. The learner does not define a function, does not use `fin_cases`, and does not verify a function's output by case analysis. The "function verification by exhaustion" pattern described in the introduction is not actually demonstrated by the proof.

**Why**: The playtest audit (r2) flagged this as P2-1 and recommended either renaming L08 or redesigning its statement. Neither has been done. The mismatch between title/introduction and actual content is a pedagogical credibility issue: if the learner reads "you will verify a function by exhaustion" and then the proof is just `norm_num`, they may feel misled or confused about what "function verification" means.

The second enrichment review (suggestion 1) noted that this gap is narrower than it first appears -- the concept of "check each input" is conveyed even if `fin_cases` is not used -- but the framing remains misleading.

**Where**: L08 title and introduction.

**Effort**: Low (rename to "Computing a function's sum" or "Evaluating a function on Fin 3" and adjust the introduction to match the actual proof experience).

**Recommend**: Yes. The fix is a text change, not a code change. Honest framing costs nothing.

---

### 6. The world lacks a level where `fin_cases` and a non-uniform closer interact -- every `fin_cases` level uses a uniform closer via `<;>`

**What**: Every level that uses `fin_cases` in this world follows the pattern `fin_cases i <;> same_closer`. The closer is always uniform: `omega` (L01, L02, L04), `norm_num` (L06, L10), or `constructor <;> norm_num` (L10). No level requires the learner to handle cases individually with the `·` bullet syntax because the same closer always works for all cases.

**Why**: The `·` case-handling syntax after `fin_cases` is introduced in L10's prose ("handle each case individually: `fin_cases i` / `· constructor <;> norm_num` / ...") but is never required. Since L10's `<;>` solution works uniformly, the learner has no incentive to try the `·` syntax. This means the world teaches the uniform-closer path thoroughly but does not give the learner any hands-on practice with non-uniform per-case handling.

This is related to suggestion 1 (L10's pedagogical mismatch) but is a distinct point: even if L10 were redesigned to require different closers, the `·` syntax should be introduced before or during the first level that needs it, not merely mentioned in prose.

However, this is a mild concern. The `·` syntax is a Lean mechanism, not a proof move, and L10's prose + hidden hints provide enough scaffolding. The learner will encounter genuine per-case handling in later worlds (W3 with lists, W5 with finsets). Introducing it here without a genuine need would be artificial.

**Where**: Relevant only if L10 is redesigned per suggestion 1. If L10's statement is changed to require non-uniform closers, the `·` syntax becomes mandatory and is naturally taught.

**Effort**: N/A (contingent on suggestion 1).

**Recommend**: Consider, but only in the context of an L10 redesign.

---

### 7. No forward reference from L09 (zero divisors) to the ring theory or number theory courses

**What**: L09's conclusion discusses zero divisors, the distinction between `Fin p` (field for prime `p`) and `Fin n` (merely a ring for composite `n`), and the connection to primality. But it does not mention that the zero-divisor concept will be formally studied in the ring_theory course (Course 6 in the catalog), or that the primality connection will appear in elementary_nt (Course 8).

**Why**: This is a cross-course foreshadowing opportunity. The learner encountering zero divisors for the first time may wonder "is this a curiosity or will it matter later?" A single sentence -- "The zero-divisor phenomenon will reappear when you study rings: it is precisely the elements that fail to have multiplicative inverses" -- would seed the vocabulary and connect this observation to the larger curriculum. The cost is one sentence; the benefit is preventing the learner from dismissing zero divisors as a finite-type quirk.

**Where**: L09 conclusion.

**Effort**: Low (one sentence).

**Recommend**: Consider. The current conclusion already does a good job of explaining the mathematical significance (prime vs. composite, field vs. ring). Adding a forward reference is nice but not necessary -- the learner is in the finite_math course and may not even proceed to ring_theory.

---

## Overall impression

**What the world does well**: The world has matured significantly across two rounds of enrichment and two rounds of playtest auditing. The P0 exploitability defects are fixed: `native_decide` is disabled everywhere, and `decide` is properly gated. The level ladder has a clear arc from introduction (L01-L03) through practice (L04-L09) to mixed application (L10) and integration (L11). The modular arithmetic block (L07, L09) is a highlight -- the subtraction wrapping, multiplication wrapping, and zero-divisor conjunction provide genuine mathematical content with minimal tactic burden. The prose quality remains consistently high: introductions motivate, conclusions consolidate, and transfer language connects Lean proofs to paper proofs. The tactic documentation (TacticDoc for `fin_cases`, `decide`, `norm_num`) is thorough.

The world's structural strengths should not be touched:
- The L01/L02 split (separate closings vs. `<;>` combinator) is pedagogically sound.
- The L03/L04 pair (introduce `decide`, then force `fin_cases` by disabling `decide`) teaches tactic selection effectively.
- The L05/L06 pair (introduce `norm_num`, then combine with `fin_cases`) mirrors the L01/L02 pattern.
- L07 and L09's modular arithmetic content is the world's best mathematical material.
- The boss (L11) is a clean two-part integration requiring planning and tactic selection.

**The single most important remaining improvement**: Fix L10's pedagogical mismatch (suggestion 1). The level promises "choosing the right closer" but delivers uniform `norm_num` for every case. Either redesign the statement to genuinely require different per-case tactics, or reframe the title and introduction to match what the level actually teaches. This is the only remaining suggestion that affects the learner's experience in a non-trivial way. The other suggestions are polish (table consistency, title accuracy, minor text changes).

**Verdict**: The world is close to clean. Suggestions 1 (L10 redesign or reframe), 3 (remove `simp_all` mention), and 5 (L08 title honesty) are the actionable items. Suggestions 2, 4, 6, and 7 are considerations that may or may not be worth the effort depending on the overall timeline. If only one change is made, it should be suggestion 1.
