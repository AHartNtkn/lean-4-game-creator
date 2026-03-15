# Enrichment Review: W3_ex (FinThreeExamples) -- Round 4

**Reviewer**: enrichment-reviewer (fourth review)
**World**: FinThreeExamples (11 levels: L01--L11)
**Position**: After FinIntro (W1, 13 levels) and FinCompute (W2, 11 levels); before ListBasics (W3)
**World type**: Example world -- concretize Fin on the specific object Fin 3

## Review of R3 suggestions

| R3 # | Suggestion | Status |
|-------|-----------|--------|
| 1 | Add named-lemma practice note to L09 | Done: L09 intro now says "Proving injectivity and surjectivity as separate named lemmas and then combining them is standard Lean practice, not just a game exercise. Breaking complex goals into smaller named pieces is how most real Lean proofs are organized." |
| 2 | Connect order to composition in L10 conclusion | Done: L10 conclusion has "Connection to composition" paragraph explaining f-circ-f = id |
| 3 | Change L11 boss statement to `Function.Bijective f` | Done: L11 statement uses `Function.Bijective` |
| 4 | Add foreshadowing to L06 conclusion | Done: L06 conclusion ends with "What about the other direction?" paragraph |
| 5 | Mention addition principle in L08 | Not done (was "Consider"). L08 conclusion mentions "sum types (alpha + beta)" as a preview but does not name the addition principle |
| 6 | Fix L10 transfer in skill table | Done: L11 skill table line 136 now reads "Swapping 1 and 2 twice returns to the original arrangement" for L10 |
| 7 | Add `NewTactic refine` to L03 | Not done (was "Consider") |
| 8 | Use consistent names for the two functions | Partially done. Introductions and conclusions consistently use "the cyclic shift" and "the swap" / "swap permutation" |
| 9 | Connect modular arithmetic interpretation to function definitions | Not done (was "Consider"). L11 intro mentions "multiplication by 2 modulo 3" for the swap, but no level explains the cyclic shift as "addition of 1 modulo 3" |

---

## Ranked Suggestions

### 1. L03 uses `refine` but it is never introduced anywhere in the course

**What**: L03 (PairingElements) instructs the learner to use `refine <(0, 1), ?_>`, and its hints explicitly say "Try `refine <(0, 1), ?_>`." However, `refine` is not declared as `NewTactic` in L03 or in any level of W1 (FinIntro) or W2 (FinCompute). This means the learner encounters a tactic they have never seen, with no documentation available in the tactic panel.

**Why**: This is a genuine inventory defect. The lean4game framework uses `NewTactic` declarations to populate the tactic documentation sidebar. A tactic that appears in hints and sample proofs but is not declared anywhere is invisible to the learner who wants to understand its semantics. `refine` is a substantive tactic -- it provides a partial term and leaves placeholders as goals -- and the learner deserves a `TacticDoc` entry explaining it. R3 suggestion 7 flagged this as "Consider." Given that (a) `refine` is not introduced in any prior world, (b) the level's hints tell the learner to use it, and (c) the `TacticDoc` is missing, this is an inventory gap that should be fixed.

**Where**: L03_PairingElements.lean: add `NewTactic refine` and a `TacticDoc refine` entry.

**Effort**: Low (add ~10 lines: a TacticDoc and a NewTactic declaration).

**Recommend**: Yes.

---

### 2. The cyclic shift's modular arithmetic interpretation is never stated, but the swap's is

**What**: L11's introduction explains that the swap `0->0, 1->2, 2->1` is "multiplication by 2 modulo 3." But nowhere in the world is the cyclic shift `0->1, 1->2, 2->0` identified as "addition of 1 modulo 3." This asymmetry means the modular arithmetic connection -- which could explain *why* the two permutations have different orders -- is incomplete.

**Why**: The modular arithmetic interpretation is not just a curiosity; it is the *explanation* for order. The cyclic shift adds 1 each time: after 3 applications you have added 3 = 0 (mod 3), returning to the identity. The swap multiplies by 2 each time: after 2 applications you have multiplied by 4 = 1 (mod 3), returning to the identity. These are genuine mathematical reasons, not just exhaustive verification. A sentence in L04's introduction (when the cyclic shift first appears) -- "This is the function `i -> i + 1 mod 3`, or equivalently, adding 1 in modular arithmetic on `Fin 3`" -- would connect the permutation work back to W2's modular arithmetic levels (L07--L09) and give the learner a conceptual explanation for the order-3 property they verify in L10.

**Where**: L04 introduction, when the cyclic shift is defined.

**Effort**: Low (add 1-2 sentences to L04 introduction).

**Recommend**: Consider.

---

### 3. L08's conclusion should name the "addition principle" alongside the multiplication principle

**What**: L08's conclusion names and explains the "multiplication principle" (`|A x B| = |A| * |B|`) and previews sum types (`alpha + beta`), function types (`alpha -> beta`), and subtypes. But it does not name the "addition principle" (`|A + B| = |A| + |B|`) as such, even though it is the most natural companion to the principle just proved.

**Why**: Naming matters for retention. The learner who finishes L08 should leave with the phrase "multiplication principle" and the awareness that there is an "addition principle" as its dual. The current preview ("sum types, function types, subtypes") is a list of types rather than a named principle. One additional sentence -- "The **addition principle** says that `|A + B| = |A| + |B|` for disjoint unions. Together, the multiplication and addition principles are the foundation of all finite counting." -- would complete the conceptual pair.

**Where**: L08 conclusion, after the multiplication principle paragraph.

**Effort**: Low (add 2 sentences).

**Recommend**: Consider.

---

### 4. L04 conclusion's "same-domain matters" paragraph could be strengthened with the equivalence

**What**: L04's conclusion says "When domain and codomain have the same size, injectivity is especially interesting -- it means the function is a permutation." This is stated as an informal observation but never connected to the formal equivalence: for finite types of equal size, injectivity, surjectivity, and bijectivity are all equivalent.

**Why**: This equivalence is one of the central facts about finite functions. The learner sees three separate proof patterns (injectivity in L04, surjectivity in L05, bijectivity in L09) without understanding that for same-size finite sets, proving any one of these implies the other two. A sentence in L04's conclusion like "In fact, for functions between finite sets of the same size, injectivity implies surjectivity (and vice versa). You will see this principle in the Counting and Pigeonhole world." would plant the seed without requiring proof, and give the later world a concrete callback.

**Where**: L04 conclusion, in the "Same-domain matters" paragraph.

**Effort**: Low (add 1-2 sentences).

**Recommend**: Consider.

---

### 5. The boss conclusion's "what you learned" skill table omits `have` from the proof-move inventory

**What**: L11's skill table (lines 109--121) lists the proof patterns for each level. The recurring pattern `have hv := congr_arg Fin.val h` is listed under the "Fin.val extraction move" column for L04, but the `have` tactic itself -- used to introduce intermediate results -- is never listed as a skill practiced in this world. The `have` tactic is the mechanism by which the learner introduces named intermediate values, and this world uses it in L03, L04, L07, L09, and L11.

**Why**: `have` is a foundational proof structuring tactic. The boss conclusion should acknowledge it as a skill the world practiced, since it was introduced in W1 but used here in a new context (introducing intermediate results for contradiction arguments, not just for direct reasoning). This is a minor omission in the skill table, not a structural gap.

**Where**: L11 boss conclusion skill table.

**Effort**: Low (add one row or note to the table).

**Recommend**: Consider.

---

### 6. L02's conclusion could note that 2i+1 is the formula for odd numbers, connecting to parity

**What**: L02 proves that `2*i + 1` is odd for each `i in Fin 3`. The conclusion verifies the three cases but does not say *why* this is true in general: `2i+1` is odd for ALL natural numbers, not just for `i in {0,1,2}`. The exhaustive check on Fin 3 happens to verify a universal fact, and this distinction between "checked for all cases of a specific finite type" and "true for structural reasons" is pedagogically important.

**Why**: The distinction between "verified by exhaustion" and "true by algebraic structure" is a recurring theme in finite mathematics. In later worlds (W14+), the learner will encounter sums and products where exhaustive checking is impossible and structural reasoning is required. A sentence in L02's conclusion like "Of course, `2i + 1` is odd for *every* natural number, not just for `i in {0, 1, 2}`. The exhaustive check here verifies a general fact on a specific small domain. In later worlds, you will prove general statements that cannot be checked case-by-case." would preview this transition and give the exhaustive method its proper context.

**Where**: L02 conclusion.

**Effort**: Low (add 2-3 sentences).

**Recommend**: Consider.

---

### 7. L01's conclusion could note that this world's disjunction-navigation is a new skill on top of `fin_cases`

**What**: L01's conclusion says "You used `fin_cases` from the Computing with Fin world. But instead of closing each case with `omega` or `norm_num`, you had to navigate a disjunction -- a different kind of work on the same structural foundation." This is a good observation, but it could be sharpened. The conclusion could explicitly name the new skill: "The proof shape is `fin_cases` + **disjunction navigation** (`left`/`right`). In the previous world, the proof shape was `fin_cases` + arithmetic closure. Swapping the closure step while keeping the structural frame is an example of **proof-move composition**."

**Why**: Naming "disjunction navigation" as a composable proof move that plugs into the `fin_cases` frame would help the learner recognize the pattern: `fin_cases` provides the structural split, and the closure step is interchangeable. This recognition will pay off throughout the world as the closure step changes (to `norm_num` in L02, to `refine + contradiction` in L03, to `rfl + exfalso` in L04, to `exact <witness, rfl>` in L05, etc.).

**Where**: L01 conclusion.

**Effort**: Low (rephrase existing sentences).

**Recommend**: Consider.

---

### 8. L05 disables `norm_num` but L04 does not -- the asymmetry is unexplained

**What**: L04 (injectivity) has `DisabledTactic trivial decide native_decide simp aesop simp_all` but allows `norm_num`. L05 (surjectivity) has `DisabledTactic trivial decide native_decide simp aesop simp_all norm_num` -- it additionally disables `norm_num`. This asymmetry is never explained in the introductions or conclusions. Since L04 relies on `norm_num at this` in its closer, the disabling makes sense there (you need `norm_num`). But the learner might wonder why `norm_num` is sometimes available and sometimes not.

**Why**: This is not necessarily a problem -- it makes sense pedagogically because L04 needs `norm_num` for the contradiction step while L05 uses only `exact` with witnesses. But a brief note in L05's introduction saying "we have disabled `norm_num` here because the surjectivity proof relies on providing exact witnesses, not numeric computation" would make the pedagogical intent visible. The tactic inventory should feel intentional, not arbitrary.

**Where**: L05 introduction.

**Effort**: Low (add 1 sentence).

**Recommend**: Consider.

---

## Overall Impression

The world is in excellent shape after four rounds of review. The 11-level arc is pedagogically sound and well-paced: L01 (enumerate) -> L02 (compute) -> L03 (construct pairs) -> L04 (inject) -> L05 (surject) -> L06 (surjection fails) -> L07 (injection fails) -> L08 (count) -> L09 (biject) -> L10 (involution) -> L11 (boss). The disabled-tactic strategy is consistent and principled. The hint structure is multi-layered. The conclusions do genuine pedagogical work -- naming proof moves (the "Fin.val extraction move"), providing plain-language transfer, connecting to the broader course (pigeonhole foreshadowing in L06-L07, permutation counting in L11), and building a skill inventory table in the boss conclusion.

The most important remaining improvements are all low-effort. The single most impactful fix is **suggestion 1** (adding `NewTactic refine` and `TacticDoc refine` to L03), because it addresses a genuine inventory gap: the learner is told to use a tactic that does not appear in their tactic panel and has no documentation. This is the only "Yes" item. All other suggestions are "Consider" items -- they would improve the world but are not required for it to function well.

The world has no remaining structural defects, no missing proof moves, no unnamed strategies that are used repeatedly, and no false statements. The improvements that remain are textual refinements that would deepen connections (modular arithmetic interpretation, addition principle, injectivity-surjectivity equivalence on same-size sets) or make existing pedagogical choices more explicit (explaining why `norm_num` is disabled in some levels but not others). The world is ready for playtest auditing.
