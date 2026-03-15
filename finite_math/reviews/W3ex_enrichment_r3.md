# Enrichment Review: W3_ex (FinThreeExamples) -- Round 3

**Reviewer**: enrichment-reviewer (third review)
**World**: FinThreeExamples (11 levels: L01--L11)
**Position**: After FinIntro (W1) and FinCompute (W2); before ListBasics (W3)
**World type**: Example world -- concretize Fin on the specific object Fin 3

## Review of R2 suggestions

All four "Yes" items from R2 have been implemented:

| R2 # | Suggestion | Status |
|-------|-----------|--------|
| 1 | Add involution level for the swap | Done (L10_Involution.lean) |
| 2 | Enumerate all 6 permutations in a conclusion | Done (L11 boss conclusion, table with descriptions and orders) |
| 3 | Acknowledge L09 repetition in the intro | Checked L09 intro -- the intro says "You will re-prove both properties for the same function. This is deliberate practice" and "the point is to combine two familiar proof moves... into a single structured proof using `constructor`." This adequately addresses the concern. |
| 4 | Name the `congr_arg Fin.val` pattern | Done (L04 conclusion names it "the **Fin.val extraction** move" with a dedicated paragraph) |
| 5 | 6 permutations table | Done (L11 boss conclusion has the full 6-row table with order annotations) |
| 6 | `omega` disabled in L01/L02 | Done (both have `omega` in DisabledTactic) |

The implementations are solid. The involution level (L10) is well-constructed: clean intro with a comparison to the cyclic shift, a simple `fin_cases i <;> rfl` proof, and a conclusion table comparing the swap and cyclic shift by order. The boss conclusion table listing all 6 permutations with descriptions and orders is exactly what was requested.

---

## Ranked Suggestions

### 1. L09 acknowledges the repetition but does not offer the key transfer sentence about named lemmas

**What**: L09's introduction says the repetition is "deliberate practice," which addresses R2 suggestion 3. But it stops short of the most valuable sentence: explaining that in a real Lean development, you would name the injectivity and surjectivity lemmas separately and combine them with `exact <inj_lemma, surj_lemma>`. The learner should understand that `constructor` + re-proving is a workaround for the game format, not standard Lean practice.

**Why**: A learner who internalizes "bijectivity proofs require re-proving both parts" has acquired a false belief about how Lean proofs work in practice. One sentence in the introduction or conclusion -- "In a real Lean file, you would prove injectivity and surjectivity as separate lemmas (`theorem shift_injective` and `theorem shift_surjective`) and then combine them with `exact <shift_injective, shift_surjective>`. In this game, each level is self-contained, so we prove both parts inline." -- would prevent this misconception while explaining why the game format forces the repetition.

**Where**: L09 introduction or conclusion.

**Effort**: Low (add 2 sentences).

**Recommend**: Yes.

---

### 2. L10's conclusion compares swap and cyclic shift orders but does not connect to composition

**What**: L10's conclusion correctly identifies order 2 vs order 3. Add one sentence noting that composing the cyclic shift with itself gives the reverse cyclic shift (the other order-3 element), and that composing any transposition with itself gives the identity. This connects order to composition without requiring a new level.

**Why**: The concept of "order" is meaningless without the operation it refers to. The conclusion says "In group theory, this is expressed by saying the swap has order 2 and the cyclic shift has order 3" -- but the word "order" presupposes a group operation (composition) that is never mentioned. One sentence like "Composing the swap with itself gives the identity (that is what 'order 2' means). Composing the cyclic shift with itself gives the reverse cyclic shift `0->2, 1->0, 2->1` -- you need a third composition to return to the identity (that is what 'order 3' means)." would ground the terminology.

**Where**: L10 conclusion, after the comparison table.

**Effort**: Low (add 2-3 sentences).

**Recommend**: Yes.

---

### 3. The boss (L11) uses `Injective f /\ Surjective f` instead of `Bijective f`

**What**: L09 introduces `Function.Bijective` and proves the cyclic shift is bijective. The boss (L11) then asks the learner to prove `Injective f /\ Surjective f` for the swap, which is structurally identical to L09 but with a different function. Using `Function.Bijective f` as the boss statement would require the learner to recall that `Bijective = Injective /\ Surjective` and unfold/apply accordingly.

**Why**: The boss is supposed to test integration. By using the raw conjunction, L11 makes the `constructor` step immediately obvious. If the statement were `Function.Bijective f`, the learner would need to recall (from L09) that `Bijective` is a conjunction, then use `constructor` or `exact <_, _>`. This is one additional recall step -- small, but it is precisely the kind of retrieval that strengthens learning. Without it, L11 is "do L09 again with a different function," which is repetitive without being integrative. R2 suggestion 9 flagged this as "consider" -- I am upgrading to "yes" because L09 now explicitly teaches `Function.Bijective` with its own `DefinitionDoc` and `NewDefinition`, so the recall is well-supported.

**Where**: L11 statement.

**Effort**: Low (change the statement type, add a brief hint about unfolding `Bijective`).

**Recommend**: Yes.

---

### 4. L06 conclusion does not foreshadow L07's dual failure

**What**: L06 proves that `Fin.castSucc : Fin 3 -> Fin 4` is not surjective. L07 proves that a function `Fin 4 -> Fin 3` is not injective. L07's conclusion explicitly connects these as "two faces of the same coin -- the pigeonhole principle." But L06's conclusion ends with the general statement about surjectivity failure and never hints that the next level will show the dual. Add a foreshadowing sentence to L06's conclusion.

**Why**: The duality between "not enough inputs to cover all outputs" (L06) and "too many inputs for the available outputs" (L07) is one of the deepest mathematical insights in this world. Currently the learner only sees the connection in retrospect (from L07's conclusion). Foreshadowing from L06 -- something like "In the next level, you will see the other face of this principle: what happens when there are *too many* inputs for the available outputs." -- would prime the learner to recognize the duality when they encounter L07.

**Where**: L06 conclusion, final paragraph.

**Effort**: Low (add 1-2 sentences).

**Recommend**: Yes.

---

### 5. L08 mentions the multiplication principle but not the addition principle

**What**: L08 proves `Fintype.card (Fin 3 x Fin 3) = 9` and its conclusion explains the multiplication principle. It does not mention the existence of the addition principle (`Fintype.card (alpha + beta) = Fintype.card alpha + Fintype.card beta`). A single sentence in the conclusion noting the addition principle would complete the conceptual pair.

**Why**: The multiplication and addition principles are the two most basic counting principles. Introducing one without even acknowledging the other leaves the conceptual picture incomplete. The learner does not need to prove the addition principle here -- just knowing it exists and will appear later (W12) is enough to complete the "counting principles come in pairs" idea. R2 suggestion 8 flagged this as "consider." Given that it costs a single sentence and completes an important conceptual pair, it merits implementation.

**Where**: L08 conclusion, after the multiplication principle paragraph.

**Effort**: Low (add 1-2 sentences).

**Recommend**: Consider.

---

### 6. The transfer column in the boss skill table has an error for L10

**What**: The boss conclusion's skill table (line 135 of L11_Boss.lean) lists the L10 transfer as "0->0, 1->2, 2->1 is both injective and surjective." This describes L11's (the boss's) mathematical content, not L10's. L10 is the involution level; its transfer should be something like "Swapping 1 and 2 twice gives back the original."

**Where**: L11 conclusion, the "key transfer insight" section.

**Effort**: Low (fix one bullet point).

**Recommend**: Yes.

---

### 7. L03 introduces `refine` but does not add it to NewTactic

**What**: L03 uses `refine <(0, 1), ?_>` as its primary proof move and hints tell the learner to use `refine`. However, the level does not declare `NewTactic refine`, which means the tactic inventory panel will not show documentation for `refine` when the learner encounters it. If `refine` was already introduced in a prior world, this is fine -- but if this is the first time the learner encounters `refine`, the missing `NewTactic` declaration means they cannot look it up in the tactic panel.

**Why**: In the lean4game framework, `NewTactic` controls what appears in the tactic documentation sidebar. A tactic used in hints but not declared as `NewTactic` (and not previously declared) will be invisible to the learner who wants to understand it. This is a discoverability issue, not a build issue.

**Where**: L03, add `NewTactic refine` if not already introduced in W1 or W2.

**Effort**: Low (one line).

**Recommend**: Consider.

---

### 8. The world uses two different functions (cyclic shift and swap) but never explicitly names them as variables

**What**: Both the cyclic shift and the swap are defined inline as anonymous lambda expressions in every level that uses them. The cyclic shift appears in L04, L05, L09, and is referenced in L10. The swap appears in L10 and L11. Neither is ever given a name (like `shift` or `swap`) in the Lean code. This means the learner sees the raw match expression `fun i : Fin 3 => match i with | 0 => (1 : Fin 3) | 1 => 2 | 2 => 0` repeatedly, without the conceptual shorthand of a name.

**Why**: The anonymous lambda is necessary because lean4game levels are self-contained and cannot share definitions. But the introductions and conclusions could consistently refer to the function by name ("the cyclic shift `sigma`" or "the swap `tau`") even if the Lean code uses the inline definition. This would help the learner build a mental model: "I proved that sigma is injective, then surjective, then bijective." Currently, the learner must re-parse the match expression each time to recognize that it is the same function.

**Where**: Introductions and conclusions of L04, L05, L09, L10, L11. Use consistent names like "the cyclic shift" and "the swap" throughout (which is partially done already, but not consistently).

**Effort**: Low (textual edits to intros/conclusions).

**Recommend**: Consider.

---

### 9. No level connects the modular arithmetic interpretation to the function definitions

**What**: L11's introduction notes that the swap is "multiplication by 2 modulo 3." L10's conclusion mentions order. But no level or conclusion notes that the cyclic shift is "addition of 1 modulo 3" -- a fact that explains why it has order 3 (since 1+1+1 = 3 = 0 mod 3). This modular arithmetic interpretation would connect the permutation work back to FinCompute (W2), which devoted three levels to modular arithmetic on Fin.

**Why**: The modular arithmetic interpretation is not decorative -- it explains *why* the cyclic shift has order 3 and the swap has order 2 in terms the learner already understands from W2. The cyclic shift is `i -> i + 1 mod 3`, so applying it 3 times adds 3, which is 0 mod 3. The swap is `i -> 2*i mod 3`, so applying it twice multiplies by 4 = 1 mod 3. These are genuine mathematical explanations of order, not just case-checking. A sentence in L10's conclusion or L04's introduction would suffice.

**Where**: L04 introduction (when the cyclic shift is first introduced) or L10 conclusion (when order is discussed).

**Effort**: Low (add 2-3 sentences).

**Recommend**: Consider.

---

## Overall Impression

The world has matured significantly across three rounds. The 11-level arc is well-structured: enumerate (L01) -> compute (L02) -> construct pairs (L03) -> inject (L04) -> surject (L05) -> surjection fails (L06) -> injection fails (L07) -> count (L08) -> biject (L09) -> involution (L10) -> boss (L11). Every level has disabled tactics that prevent trivial automation. The hint structure is consistently multi-layered (visible hints for the next step, hidden hints for the full closer). The conclusions do genuine pedagogical work: naming proof patterns (the "Fin.val extraction move"), providing transfer moments ("In plain language..."), and building connections (the 6 permutations table). The involution level (L10) and the 6-permutation table (L11) were the most impactful R2 additions, transforming the world from a collection of isolated function-property exercises into a study of two mathematically distinct permutations.

The world's remaining improvements are all low-effort textual edits rather than structural changes. The single most important improvement is **suggestion 1** (adding the "in a real Lean file, you would name lemmas separately" sentence to L09), because it prevents a false belief about Lean practice that the game format would otherwise teach. The second most impactful is **suggestion 3** (changing the boss statement to `Bijective f`), which would turn the boss from "L09 again with a different function" into "recall that bijective = injective + surjective, then prove both parts" -- a genuine integration test rather than a repetition. Neither requires more than a few lines of change.
