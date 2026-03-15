# W4_ex ListUnderLenses -- Enrichment Review (Round 2)

**World**: ListUnderLenses (6 levels)
**Type**: Example world (concretizes W4 MultisetHierarchy)
**Concrete object**: The list `[1, 2, 1, 3]`
**Reviewer**: Enrichment reviewer, fresh context
**Prior review**: R1 enrichment + R1 playtest

---

## Changes since R1

The world grew from 5 to 6 levels:
- **L01**: Now includes membership (`2 ∈ list`) -- was R1 suggestion #4's counterpart for the list lens.
- **L02**: Now explains why `rfl` works for cardinality but not membership; includes `Multiset.mem_coe` bridge.
- **L04**: Now proves **both** multiset equality and finset equality (same-finset proof added).
- **L05 (new)**: Dedicated level for `Multiset.card_map` -- mapping preserves cardinality.
- **L06 (boss)**: Expanded to 5-part conjunction including `card_map` and `toFinset_card_le`.

L05 disables both `decide` and `norm_num`, making the bridge-lemma lesson enforced. This is the only level that disables `decide`.

---

## R1 item disposition

| R1 # | Suggestion | Status | Notes |
|-------|-----------|--------|-------|
| 1 | Add `Multiset.count` level | **NOT DONE** | Still missing. See suggestion 1 below. |
| 2 | Add `List.toFinset` shortcut level | **NOT DONE** | Neither the shortcut nor the two-path equivalence is shown. |
| 3 | Transfer moment is passive text, not active proof | **PARTIALLY DONE** | The boss conclusion has a richer transfer section, but the transfer is still prose in a conclusion, not a proved statement. |
| 4 | L03 never exercises `Finset.mem` | **NOT DONE** | L03 still has only `toFinset = {1,2,3}` and `card = 3`. No membership conjunct. |
| 5 | No non-membership level | **NOT DONE** | No `4 ∉ list` anywhere. |
| 6 | Reduce-then-compute pattern not labeled in hints | **PARTIALLY DONE** | L02 conclusion names the pattern clearly. L04 hints do not label the steps as "Step 1 (Reduce)" / "Step 2 (Compute)" -- they just say "use this lemma, then decide." |
| 7 | `Multiset.count` permutation-invariance not proved | **NOT DONE** | Still claimed in L04 conclusion but unproved. |
| 8 | Boss is a gauntlet | **IMPROVED** | Now 5 parts instead of 4, with `card_map` and `toFinset_card_le` adding variety. But still no part depends on another part's result. |
| 9 | No foreshadowing of W5 | **DONE** | L06 conclusion mentions "constructing them" and "set operations" in the next worlds. |
| 10 | L01 intro doesn't distinguish from W4 L10 | **NOT DONE** | L01 intro still doesn't acknowledge the revisitation. |

---

## Ranked suggestions

### 1. `Multiset.count` level is still missing -- the hierarchy's key distinguishing operation

**What**: Add a level (between L02 and L03) where the learner proves `Multiset.count 1 (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) = 2`. Then the L03 conclusion (or a brief sentence in L03's introduction) should contrast: "In the multiset, `1` has count 2. In the finset, there is no count -- only membership. This is the information that `toFinset` discards."

**Why**: This was the #1 R1 suggestion and the "single most important improvement." The rationale has not changed: the hierarchy's central distinction is multiplicity. The world proves cardinality drops from 4 to 3 but never shows *which element's multiplicity is lost* or *what count means concretely*. `Multiset.count` is the API that makes multiplicity tangible. W4 L06 introduced `Multiset.count` on this exact list -- the example world should revisit it, because the contrast between "count 1 = 2 as a multiset" and "1 is just a member as a finset" is the entire point of the hierarchy. Without this level, the information-loss story is numerical (4 vs 3) rather than elemental (1 appears twice vs 1 just belongs).

**Where**: New level between L02 and L03 (becomes new L03; current L03-L06 shift to L04-L07).

**Effort**: High (new level).

**Recommend**: Yes.

---

### 2. L03 should include finset membership to complete the three-lens parallel

**What**: Add `(2 : Nat) ∈ (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset` as a third conjunct to L03.

**Why**: This was R1 suggestion #4 and remains unaddressed. L01 proves `length = 4 ∧ 2 ∈ list`. L02 proves `card = length ∧ 2 ∈ multiset`. L03 proves `toFinset = {1,2,3} ∧ card = 3` -- but no membership. The parallel structure is broken. Adding the membership conjunct costs one `decide` (or `Finset.mem_toFinset.mpr (Multiset.mem_coe.mpr (by decide))` if `decide` is disabled, though here `decide` is available on L03). The symmetry is not decorative -- it is what enables the conclusion to show a clean comparison table: "membership holds in all three lenses; cardinality drops only at the finset stage."

**Where**: Modify L03 statement and add one hint.

**Effort**: Low (one conjunct).

**Recommend**: Yes.

---

### 3. `decide` is not disabled on L01, L02, L03, L04, or L06 -- only L05 enforces bridge lemmas

**What**: Disable `decide` on L02, L04, and L06 (the levels where the intended lessons are bridge-lemma usage).

**Why**: The R1 playtest audit identified this as P0: `decide` closes every level without engaging with bridge lemmas. The revisions since R1 disabled `decide` on L05 (good), but L02 (`Multiset.mem_coe`), L04 (`Multiset.coe_eq_coe`), and L06 (boss, which integrates both bridge lemmas plus `toFinset_card_le`) still allow `decide` to bypass everything. The fundamental tension (the intended proof is `rw [bridge]; decide`, so disabling `decide` breaks the intended proof too) has a known resolution: restructure the proof so the `decide` step comes AFTER the rewrite. On L02, for example, once `rw [Multiset.mem_coe]` is applied, the remaining goal `2 ∈ [1, 2, 1, 3]` can be closed by other means (e.g., keep `decide` enabled only after the rewrite fires, or use `exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))`). However, this is fundamentally a structural design choice, not an enrichment opportunity. I note it because it remains the most severe open issue from R1 and would substantially improve the world's pedagogical value if resolved.

**Where**: L02, L04, L06 DisabledTactic lines.

**Effort**: Medium (requires testing that the intended proofs still work with `decide` disabled, and potentially restructuring some hints to use alternative closers).

**Recommend**: Yes.

---

### 4. No inventory declarations in the entire world

**What**: Add `NewTheorem` declarations for the bridge lemmas the world uses: at minimum `Multiset.mem_coe` (L02), `Multiset.coe_eq_coe` (L04), `Multiset.card_map` (L05), `Multiset.toFinset_card_le` (L06).

**Why**: This was R1 playtest P1-2. The world has zero `NewTactic`, `NewTheorem`, or `NewDefinition` declarations. Even as an example world that revisits W4 material, the inventory panel should surface the theorems the learner needs. When the learner reaches L06's boss and needs `toFinset_card_le`, there is nothing in the inventory to remind them. Adding `NewTheorem` costs nothing and makes the world self-contained for a learner who jumps in after a break.

**Where**: L02, L04, L05, L06 -- one `NewTheorem` line per level.

**Effort**: Low (one line per level + corresponding `TheoremDoc` if not already defined in W4).

**Recommend**: Yes.

---

### 5. The reduce-then-compute label should appear in the hints, not just the conclusions

**What**: In L02 and L04 hints, explicitly label the two steps: "**Step 1 (Reduce)**: `rw [Multiset.mem_coe]`" and "**Step 2 (Compute)**: `decide`."

**Why**: This was R1 suggestion #6, partially addressed (L02 conclusion names the pattern, but the hints do not). The learner reads hints *during* the proof, not after. If the hint says "use `rw [Multiset.mem_coe]` to reduce multiset membership to list membership" without saying "this is Step 1 of the reduce-then-compute pattern," the learner may not connect the technique to the named strategy. One sentence in each hint is enough: "This is the **reduce** step of the reduce-then-compute pattern." Followed later by: "This is the **compute** step."

**Where**: L02 hints (after `rw [Multiset.mem_coe]` hint and before `decide` hint), L04 hints similarly.

**Effort**: Low (a few words in existing hint text).

**Recommend**: Yes.

---

### 6. L01 introduction should acknowledge the revisitation from W4

**What**: Add 1-2 sentences to L01's introduction: "In the Multisets and Hierarchy world, you proved these facts inside a large conjunction. Here, you will explore each lens separately, with more attention to what each representation keeps and what it discards."

**Why**: This was R1 suggestion #10. Without it, a learner coming directly from W4 may feel they are re-doing the same work. The meta-commentary primes them to look for new insights (the contrast, the transfer, the pattern names) rather than viewing the world as a mechanical replay. This is especially important because L01's proof (`constructor; rfl; decide`) is identical to part of W4 L10.

**Where**: L01 introduction, after the "three lenses" list.

**Effort**: Low (2 sentences).

**Recommend**: Yes.

---

### 7. `List.toFinset` shortcut is never shown -- a missed connection to W4 L09

**What**: Add a conjunct to L03 (or a brief mention in L03's introduction) showing that `([1, 2, 1, 3] : List Nat).toFinset = {1, 2, 3}` -- the direct `List.toFinset` path -- and note that this is equivalent to the two-step pipeline `(↑list).toFinset`.

**Why**: This was R1 suggestion #2. W4 L09 introduced `List.toFinset` as the shortcut that combines coercion and deduplication. The example world always goes through the explicit `↑` then `.toFinset` path. Showing the shortcut gives the learner two spellings for the same operation and reinforces that the two-step pipeline has a one-step alias. If adding a full level is too much, a single conjunct `([1, 2, 1, 3] : List Nat).toFinset = (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset` (closable by `rfl`) would suffice.

**Where**: L03 (additional conjunct or sentence in introduction).

**Effort**: Low-Medium (one conjunct or a new mini-level).

**Recommend**: Consider.

---

### 8. Non-membership is never exercised

**What**: Add a conjunct somewhere (L01 or L03) showing `(4 : Nat) ∉ ([1, 2, 1, 3] : List Nat)` or `4 ∉ (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset`.

**Why**: This was R1 suggestion #5. The world only exercises positive membership. A "what about an element that is NOT in the list?" moment is natural and previews W6 (Membership). It also tests that the learner understands `decide` can verify non-membership (or that `Multiset.mem_coe` works for negative membership too). The proof is trivial (`decide`), but the concept is valuable.

**Where**: L01 (third conjunct) or L03 (fourth conjunct).

**Effort**: Low (one conjunct).

**Recommend**: Consider.

---

### 9. The boss still has no step that depends on a previous step's result

**What**: Restructure one part of the L06 boss so that it uses `have` to name an intermediate result that is reused in a later conjunct. For example: first prove `have h : Multiset.card (↑([1,2,1,3] : List Nat)) = 4 := rfl`, then use `h` in the inequality part (rewriting the RHS of `toFinset_card_le` to `4` using `h`).

**Why**: The R1 review (both enrichment #8 and playtest #4a) noted the boss is a gauntlet -- five independent conjuncts solved by replaying earlier techniques in sequence. The addition of `card_map` and `toFinset_card_le` improved variety, but the conjuncts remain independent. A single `have` step that connects two parts would introduce a genuine integration moment: "use the result you just proved to simplify the next goal." This is a more interesting proof structure than five independent obligations.

**Where**: L06 boss proof.

**Effort**: Medium (restructure proof and hints).

**Recommend**: Consider.

---

## Overall impression

**What the world does well**: The world has improved materially since R1. The new L05 (card_map) adds a distinct proof shape to the world's repertoire and is the only level that properly disables `decide` and `norm_num`, making the bridge-lemma lesson genuinely enforced. The L06 boss is more varied than the old L05 boss (5 parts instead of 4, with two different kinds of non-`decide` proofs). The conclusions remain excellent -- the ASCII hierarchy diagrams, the comparison tables, and the "In plain language" sections are the strongest pedagogical feature of this world. The L02 explanation of why `rfl` works for cardinality but not membership is a genuinely good teaching moment that was not in the R1 version.

**The single most important improvement**: The `Multiset.count` level (suggestion 1) is still the highest-impact missing piece. The world's narrative is "one object, three lenses -- what does each lens keep and what does it discard?" But it never exercises the operation that most directly answers that question. `Multiset.count` is the API where multiplicity lives; without it, the hierarchy's information-loss story is told entirely through cardinality numbers (4 vs 3) rather than through the concrete experience of seeing `count 1 = 2` in the multiset and then seeing that `count` does not exist for finsets. Adding this level would transform the world from "the cardinalities are different" to "here is exactly what information was lost and where."

The second priority is suggestion 3 (disabling `decide` on L02, L04, L06). The `decide` exploit remains the world's most significant structural weakness: on 5 of 6 levels, a learner can type `decide` and never engage with any bridge lemma. L05 shows that the solution is feasible -- it disables `decide` and `norm_num` and the intended `rw [Multiset.card_map]` proof works perfectly. Extending this approach to L02 and L04 would make the world's intended lessons actually enforced.
