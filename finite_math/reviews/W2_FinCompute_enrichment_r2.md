# Enrichment Review (Second Pass): W2 FinCompute ("Computing with Fin")

Reviewer: lean4game-enrichment-reviewer
Date: 2026-03-14
World files: L01_FinCases through L11_Boss (11 levels)
Context: W1 (FinIntro, 13 levels), course plan at PLAN.md, first enrichment review at reviews/W2_FinCompute_enrichment.md

---

## Status of first-review suggestions

Before looking for new opportunities, I verified which first-review suggestions were addressed by the re-authoring.

| # | First-review suggestion | Status |
|---|------------------------|--------|
| 1 | Rewrite L07 to teach V19 (function definition by cases on Fin) | **Partially addressed.** L08 ("Verifying a function on Fin by cases") introduces "function verification by exhaustion" and computes a sum of function outputs. However, the learner never *defines* a function on `Fin n` by case-splitting --- they evaluate an explicit formula `i.val ^ 2 + 1` at each input. The V19 proof move (constructing data by cases) is not fully taught. See suggestion 1 below. |
| 2 | Add subtraction wrapping level | **Fully addressed.** L07 proves `(1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5)` with excellent prose about clock arithmetic. |
| 3 | Make L04 discriminating between `decide` and `fin_cases` | **Addressed.** L04 disables `decide` and forces `fin_cases`. The prose explains when each is appropriate. |
| 4 | Show `decide` failing or being slow | **Partially addressed.** L04 disables `decide` rather than letting the learner experience failure. This is a design choice, not a gap. |
| 5 | Boss should require `decide` | **Fully addressed.** L11 boss is a conjunction: part 1 needs `decide`, part 2 needs `fin_cases` + `norm_num`. |
| 6 | Misconception/counterexample level for modular arithmetic | **Addressed.** L09 shows multiplication wrapping and discusses zero divisors and prime vs composite moduli. |
| 7 | `<;>` named as general tool | **Fully addressed.** L02 title is "The semicolon combinator" and the prose explains generality with examples. |
| 8 | Cross-world foreshadowing for `decide` | **Addressed.** L03 conclusion mentions decidable predicates in finsets. |
| 9 | `norm_num` introduced with goal `omega` can't solve | **Fully addressed.** L05 proves `(3 : Fin 10).val ^ 2 = 9`, which involves `^`. |
| 10 | Transfer moment | **Addressed.** L08 and L11 both have transfer paragraphs. |
| 11 | World-level introduction | **Not addressed.** `FinCompute.lean` is still just imports. See suggestion 4 below. |
| 12 | Named strategy ("exhaustive verification") | **Fully addressed.** L01 names the pattern "exhaustive verification" and subsequent levels reference it. |

---

## Ranked suggestions (second pass)

### 1. L08 teaches "function verification" but the learner never constructs or reasons about a case-defined function --- V19 is still partially uncovered

**What**: L08 proves `(0 : Fin 3).val ^ 2 + 1 + ((1 : Fin 3).val ^ 2 + 1) + ((2 : Fin 3).val ^ 2 + 1) = 8`. The function `f i = i.val ^ 2 + 1` is given as a formula, not defined by case-matching. The proof is a single `norm_num`. The learner never encounters a function defined via `match` or `if`/`then`/`else` on `Fin n`, never sees `fin_cases` used to reason about such a function, and never verifies that a case-defined function produces specific outputs. The plan's V19 (recursive/inductive construction over `Fin n`) calls for the learner to *build* a function by cases, not just evaluate a formula.

**Why**: The distinction matters because in W3_ex (level 2: "A function on `Fin 3`"), the learner will define and compute with a specific function `Fin 3 -> Nat`. If that function is defined by `match i with | 0 => ... | 1 => ... | 2 => ...` and the learner has never seen this pattern, they will be confronting new syntax and a new proof move simultaneously. A level in W2 that has the learner prove something about a function defined via `fun i => if i = 0 then 5 else if i = 1 then 3 else 7` (using `fin_cases` to reduce each `if`) would teach the case-definition-then-verification workflow.

That said, this is a weaker concern than in the first review. L08 does teach the mental model of "check each input," and the formula-based function `i.val ^ 2 + 1` is a legitimate function on `Fin n`. The gap is narrower: it is about the *syntactic form* of case-defined functions in Lean, not about the *concept* of verifying a function by exhaustion. If W3_ex's level 2 provides adequate scaffolding for the `match` syntax, this gap may be acceptable.

**Where**: Modify L08 to use a function defined via `if`/`then`/`else` or `match` rather than a single formula. Or add a level between L08 and L09. Alternatively, accept the gap and ensure W3_ex scaffolds the syntax.

**Effort**: Medium (modify one level's statement and proof).

**Recommend**: Consider. The concept is taught; the syntax gap is real but may be addressed downstream.

---

### 2. L10 ("Choosing the right closer") does not actually require choosing --- `norm_num` handles all cases uniformly

**What**: L10's introduction promises to teach the skill of handling cases individually when `<;>` doesn't work because different cases need different tactics. But the actual goal (`∀ i : Fin 3, i.val ^ 2 + i.val + 1 > 0`) is solved by `fin_cases i <;> norm_num`, with `norm_num` handling every case identically. The introduction even acknowledges this: "Here `norm_num` works for all cases, so `<;>` is fine. But practice using individual case handling to build the skill."

**Why**: Asking the learner to "practice" a skill on a goal that doesn't require it is pedagogically weak. The learner will (correctly) use `<;> norm_num` and never actually write individual case handlers. To genuinely teach "different closers for different cases," the goal should require it. For example, a goal where one case needs a rewrite step (like `rw [Fin.val_zero]` or referencing a hypothesis) before `norm_num`, while other cases close directly. This would force the learner to write the `·` case blocks.

Alternatively, if the point is to preview the syntax for individual case handling (the `·` bullets after `fin_cases`), a goal that is mechanically easier but *syntactically requires* per-case handling would work --- for instance, a conjunction where the left conjunct is arithmetic and the right conjunct references a different lemma in each case.

**Where**: Modify L10's statement to one that genuinely requires different tactics per case.

**Effort**: Medium (redesign one level's statement).

**Recommend**: Yes. This is the world's weakest level because its stated pedagogical goal (mixed closers) is not achieved by its actual content.

---

### 3. The modular arithmetic block (L07, L09) is pure `decide` --- the learner never connects modular results to `Fin.val` or the underlying definition

**What**: Both L07 and L09 are solved by `decide`. The learner verifies `(1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5)` and `(2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4)` without ever seeing *why* these equalities hold in terms of the `Fin` representation. The prose explains the modular arithmetic ("because `1 - 3 ≡ -2 ≡ 3 (mod 5)`"), but the proof is a black box. The learner never writes `Fin.ext`, never computes `Fin.val` on both sides, never sees the `% n` operation.

**Why**: This matters because the world's conclusion says the learner understands modular arithmetic on `Fin n`. But understanding means more than verifying facts by brute force. If a learner were asked "why does `(1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5)`?", they could only say "because `decide` said so." They could not give a value-level argument. A single level that unfolds the proof --- using `Fin.ext` to reduce to a `.val` equality, then `norm_num` or `omega` to verify the arithmetic --- would connect the modular arithmetic to the `Fin` representation taught in W1. This would also preview `Fin.ext` (subtype extensionality) as a proof technique.

That said, the prose in L07 and L09 does explain the arithmetic clearly. The gap is between the learner's *reading* of the explanation and their *doing* of the computation. Since the course is a game (learning by doing), at least one modular arithmetic level should require a multi-step proof.

**Where**: Add a short level between L07 and L08, or between L09 and L10, where `decide` is disabled and the learner proves a modular equality via `Fin.ext` + `norm_num` (or `simp` + `omega`). This grounds the modular arithmetic in the `Fin` internals.

**Effort**: High (new level).

**Recommend**: Consider. The black-box `decide` proofs are legitimate for teaching "use `decide` for concrete computations," and the prose provides the conceptual grounding. But one hands-on level connecting the computation to `Fin.val` would be higher quality.

---

### 4. The world file has no world-level introduction or conclusion

**What**: `FinCompute.lean` contains only imports. The game engine (lean4game) supports `WorldIntroduction` and `WorldConclusion` blocks in the world file. Without these, the learner enters the world with no orientation beyond the first level's introduction.

**Why**: L01's introduction does provide context ("In the previous world, you proved properties of `Fin n` elements using `intro` and `omega`. But there is a much more direct approach..."). This is adequate but not ideal. A world-level introduction would set expectations for the entire arc: "You will learn three new tactics (`fin_cases`, `decide`, `norm_num`), explore modular arithmetic on `Fin n`, and build the *exhaustive verification* proof pattern." This frames the journey before the learner encounters individual levels.

**Where**: Add `WorldIntroduction` and `WorldConclusion` blocks to `FinCompute.lean`.

**Effort**: Low (a few sentences in the world file).

**Recommend**: Consider. L01 already provides entry context, and L11 provides a comprehensive summary. Adding world-level text is polish, not substance.

---

### 5. L09's conclusion mentions `(2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4)` as a zero-divisor example but never lets the learner prove it

**What**: L09's conclusion says: "In fact, `(2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4)`, because `4 mod 4 = 0`. So `2` multiplied by itself gives `0`!" This is a striking fact --- a nonzero element whose square is zero --- but the learner only reads about it.

**Why**: The zero-divisor phenomenon is the most conceptually important aspect of modular arithmetic. It is what distinguishes `Fin p` (a field) from `Fin n` for composite `n` (merely a ring). The conclusion discusses this at length, including the connection to primality and fields. But the learner's only interaction with multiplication is proving `2 * 3 = 2`. If L09 were a conjunction --- `(2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4) ∧ (2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4)` --- the learner would prove both facts, making the zero-divisor claim experiential rather than declarative. The proof is still `decide` for both conjuncts, so the tactic burden is minimal; the mathematical content is the payoff.

**Where**: Modify L09's statement to include the zero-divisor equality as a second conjunct.

**Effort**: Low (add one conjunct to the statement, add `constructor` and `decide` to the proof).

**Recommend**: Yes. The current conclusion makes a strong mathematical claim that the learner should verify themselves. Adding one conjunct costs almost nothing and makes the world's best mathematical observation interactive.

---

### 6. The tactic trio table appears three times (L05, L10, L11) with slight variations --- this could be more consistent

**What**: L05's conclusion has a "tactic trio" table. L10's conclusion has a "closing tactics after fin_cases" list. L11's conclusion has both a tactics table and a "tactic selection hierarchy" table. The three presentations use slightly different formats and slightly different categories. For instance, L05 says `decide` is for "decidable propositions on finite types," while L11 says "concrete equality/inequality on small `Fin n`." These are not contradictory, but the evolving framing might confuse a careful reader.

**Why**: Repetition of summary tables is good pedagogy (spaced retrieval). But inconsistent wording across repetitions can undermine the learner's sense of having a stable mental model. Aligning the three presentations --- using the same column headers, the same tactic descriptions, and clearly noting when the table is being *extended* (L10 adds "Manual reasoning") --- would make the repetition a strength rather than a source of ambiguity.

**Where**: Harmonize the tables across L05, L10, and L11 conclusions. The fullest version (L11) should be the canonical one; L05 and L10 should be progressive subsets of it.

**Effort**: Low (text edits in conclusions).

**Recommend**: Consider. This is a polish issue. The current inconsistencies are minor and unlikely to confuse most learners.

---

## Overall impression

**What the world does well**: The re-authoring addressed every major concern from the first review and produced a significantly better world. The level count grew from 8 to 11, and the new levels fill genuine gaps:

- L02 (semicolon combinator) is now a proper level with its own title and explanation of `<;>` as a general tool, not just a footnote in L01.
- L05 (norm_num) now uses a goal with `^` that `omega` cannot solve, properly motivating the new tactic.
- L07 (modular subtraction) and L09 (modular multiplication) together give modular arithmetic real depth, with the clock-arithmetic metaphor, the zero-divisor discussion, and the prime-vs-composite distinction.
- L08 (function on Fin) introduces the "function verification by exhaustion" concept and foreshadows `Finset.sum`.
- L11 (boss) is a genuine integration challenge requiring `constructor`, `decide`, and `fin_cases` + `norm_num` in combination.

The prose quality is consistently high. Introductions motivate, conclusions consolidate, and the exhaustive verification pattern is named and reinforced across levels. The tactic selection hierarchy (decide / fin_cases + closer / isLt + omega) is clearly articulated. Transfer paragraphs in L07, L08, and L11 connect the Lean work to paper proofs.

**The single most important remaining improvement**: Make L09 include the zero-divisor conjunct `(2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4)` (suggestion 5). This is the world's strongest mathematical observation, it is currently only prose, and making it interactive costs one extra `constructor` + `decide`. Secondary to this, L10 should be revised to genuinely require different closers per case (suggestion 2), since its current statement does not achieve its stated pedagogical goal.

The world is in good shape. The suggestions above are refinements, not structural concerns. After addressing suggestions 2 and 5 (and optionally 1), the world will be ready for playtest auditing.
