# W11 FintypeClass -- Enrichment Review (Round 1)

**Reviewer**: enrichment-reviewer
**Date**: 2026-03-15
**World**: W11 FintypeClass (Lecture, 8 levels)
**World promise**: The learner understands `Fintype` as the type class that equips a type with a universal finset, and can use `Finset.univ` and `Fintype.card`.

---

## Ranked suggestions

### 1. Missing `NewTheorem` / `TheoremDoc` for `Fintype.card_fin` and `Fintype.card_prod`

**What**: L04 introduces and teaches `Fintype.card_fin`; L06 introduces and teaches `Fintype.card_prod`. Neither has a `NewTheorem` declaration or `TheoremDoc`. The learner's inventory panel will not show these lemmas even though they are the dominant tools for L04, L06, and L08.

**Why**: This is not cosmetic. Without `NewTheorem`, the lemmas do not appear in the inventory sidebar. The learner who forgets the exact name between levels has no way to look them up. The boss level (L08) requires both lemmas, so a learner arriving at L08 without the inventory entries may feel stuck. This is the single most impactful fix.

**Where**: L04 (add `NewTheorem Fintype.card_fin`, `TheoremDoc Fintype.card_fin as "Fintype.card_fin" in "Fintype"`), L06 (add `NewTheorem Fintype.card_prod`, `TheoremDoc Fintype.card_prod as "Fintype.card_prod" in "Fintype"`).

**Effort**: Low (add declaration blocks, analogous to L03 and L05).

**Recommend**: Yes.

---

### 2. `simp` is not disabled, creating an exploit across the entire world

**What**: The `DisabledTactic` line on every level is `trivial decide native_decide aesop simp_all`. Notably, `simp` is absent. The project memory records that the standard disabled set should include `simp`. In this world, `simp` can close L01 (`simp`), L02 (`simp`), L03 (`simp`), L04 (`simp`), L05 (`simp`), and L08 (`simp [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]`). The only levels where `simp` alone might not trivially close things are L07 (conjunction) and L06 (where `simp` is the *intended* step after `rw [Fintype.card_prod]`).

**Why**: If `simp` is available, a learner can bypass every level without learning the individual lemma names. This undermines the pedagogical goal of the world, which is to build familiarity with `Finset.mem_univ`, `Finset.card_univ`, `Fintype.card_fin`, `Fintype.card_bool`, and `Fintype.card_prod` as named tools.

**Where**: All 8 levels. Add `simp` to the `DisabledTactic` line. For L06, which currently uses `simp [Fintype.card_fin]` as its proof step, the proof needs to be restructured to use `rw [Fintype.card_fin, Fintype.card_fin]` (or two sequential rewrites) instead.

**Effort**: Low (add one word to each DisabledTactic line, restructure L06 proof to avoid `simp`).

**Recommend**: Yes.

---

### 3. L06 uses `simp [Fintype.card_fin]` as a teaching step, conflating a power tactic with the lesson

**What**: L06's intended second step is `simp [Fintype.card_fin]`. The hint says "use `simp [Fintype.card_fin]` to handle both at once." This teaches `simp` usage, not `Fintype.card_fin` application.

**Why**: The dominant lesson of L06 is `Fintype.card_prod` and the multiplication principle. Using `simp` to close the arithmetic muddles the lesson. The learner should explicitly rewrite both occurrences of `Fintype.card_fin` (e.g., `rw [Fintype.card_fin, Fintype.card_fin]`) and then see the arithmetic goal `2 * 3 = 6` close. This makes the multiplication principle visceral: you see the numbers, you see the product. With `simp` it all vanishes at once and the learner sees nothing.

**Where**: L06 -- restructure proof and hints.

**Effort**: Medium (rewrite hints and proof).

**Recommend**: Yes.

---

### 4. L07 does not actually demonstrate the `Nat` failure -- it proves something about `Bool`

**What**: L07 is titled "Nat is NOT a Fintype" and the introduction explains why `Finset.univ : Finset Nat` fails. But the actual proof goal is `(forall b : Bool, b in Finset.univ) and (Finset.univ : Finset Bool).card = 2` -- a fact about `Bool`. The learner never directly encounters the `Nat` failure. The "counterexample" is presented entirely in prose.

**Why**: This is a missed experiential teaching moment. The plan says the dominant lesson is "Counterexample" (E14) and "Set.Finite vs Fintype vs Finset distinctions" (M35). Currently, the learner is *told* about the Nat failure but never *sees* it. A level that uses `sorry` or a structured demonstration (e.g., having the learner attempt to state something about `Nat` and observe the error, or proving `Not (Finite Nat -> True)` in a controlled way) would make the concept concrete. At minimum, the level could be restructured so the learner proves something *contrasting* Bool (which works) with Nat (which doesn't), rather than just re-proving Bool facts.

**Where**: L07 -- restructure to include a genuine Nat interaction.

**Effort**: High (would require designing a level that makes the `Fintype Nat` failure interactive rather than textual). One option: have the learner prove `Fintype.card Bool < Fintype.card Bool + 1` (trivial, but uses Fintype on Bool), then add a conclusion that says "Try replacing Bool with Nat -- Lean refuses" with a `#check` block showing the error. Another option: provide a `sorry`-based scaffold where the learner sees the error message when trying to fill in a proof about Nat.

**Recommend**: Consider. The current design is not wrong -- it does teach the concept via prose -- but the experiential gap is real.

---

### 5. No `Fintype.card_sum` level despite the conclusion of L05 promising it

**What**: L05's conclusion lists the pattern of cardinality lemmas and says "`Fintype.card_sum` for sum types" is coming. But the world has no sum-type level. The plan places `Fintype.card_sum` in W12 L01.

**Why**: The promise in L05's conclusion creates an expectation. The learner reads "Fintype.card_prod for product types (coming next)" and "Fintype.card_sum for sum types" and expects both in this world. Only products appear. This creates a mild pedagogical discontinuity. Two options: (a) add a sum-type level (between L06 and L07), or (b) edit L05's conclusion to say sum types will be covered in a later world, not "and many more" in a way that implies they're coming in this world.

**Where**: L05 conclusion text.

**Effort**: Low if just editing the text; High if adding a level.

**Recommend**: Consider. Editing the L05 conclusion to clarify "sum types will appear in a later world" is the minimum fix. Adding a sum-type level would be pedagogically stronger (the addition principle parallels the multiplication principle), but the plan defers it to W12.

---

### 6. No `Fintype.card` definition/doc entry

**What**: `Fintype.card` is a central concept of this world (introduced in L03, used in L04-L08) but has no `DefinitionDoc` or `NewDefinition` entry. Only `Fintype` and `Finset.univ` are declared as new definitions in L01.

**Why**: `Fintype.card` is arguably the *most important output* of the `Fintype` class from the learner's perspective. It should have a `DefinitionDoc` entry explaining what it is and when to use it, parallel to the `Finset.univ` definition doc. Without it, the learner's definition panel has no entry for the concept that drives the entire second half of the world.

**Where**: L03 (where `Fintype.card` is introduced).

**Effort**: Low (add `DefinitionDoc` and `NewDefinition`).

**Recommend**: Yes.

---

### 7. The world lacks a "type class synthesis" teaching moment

**What**: The introduction to L01 explains `Fintype` as a type class and L06 mentions that "Lean synthesizes the Fintype instance for Fin 2 x Fin 3 by combining the instances." But no level makes the learner *experience* type class synthesis. The learner never has to think about where the instance comes from.

**Why**: Type class synthesis is a central Lean concept. This world is the ideal place to show it concretely. A level or enriched hint could ask: "Why does `Fintype.card (Fin 2 x Fin 3)` work? Because Lean combines `Fintype (Fin 2)` and `Fintype (Fin 3)` using the instance `instFintypeProd`. You don't need to provide this -- Lean finds it automatically." This would connect to the `DecidableEq` analogy already mentioned in L07 and make the analogy explicit rather than hand-waved.

**Where**: L06 conclusion or a dedicated hint in L06.

**Effort**: Low (add a paragraph to L06's conclusion explaining the synthesis chain).

**Recommend**: Consider.

---

### 8. L01 and L03 are both closable by `rfl` -- the world teaches `rfl` solutions before introducing the named lemmas

**What**: L01's goal `(Finset.univ : Finset (Fin 3)).card = 3` is closable by `rfl`. L03's goal `(Finset.univ : Finset (Fin 5)).card = Fintype.card (Fin 5)` is also closable by `rfl`. The learner who discovers this may adopt the habit of trying `rfl` on every cardinality goal, bypassing the named lemmas entirely.

**Why**: The `rfl` exploit is a known P2 issue (cannot disable `rfl`). But the current level ordering exacerbates it: L01 *explicitly teaches* `rfl` ("Try `rfl`"), so the learner is primed to use `rfl` on L02, L03, L04, and L05 as well. Consider restructuring L01 so that `rfl` is not the primary taught approach -- instead, teach a proof that goes through `Finset.card_univ` and `Fintype.card_fin` (even if `rfl` also works), and relegate `rfl` to a "note: `rfl` also works here because Lean can compute this" remark.

**Where**: L01 introduction and hints.

**Effort**: Medium (rewrite L01's pedagogical framing so the primary path uses named lemmas, with `rfl` as a noted alternative rather than the taught strategy).

**Recommend**: Consider. The fundamental issue (`rfl` on decidable equalities) is accepted as P2. But teaching `rfl` first in L01 maximizes the exploit surface. If L01 instead taught "use `Finset.card_univ` and `Fintype.card_fin`", those tools would be introduced earlier and the learner would be primed to use named lemmas.

---

### 9. No transfer moment in the world (only in the boss conclusion)

**What**: The plan mentions coverage items T-series but the world has no explicit "Transfer moment" section (unlike W10_ps which has one). The L08 conclusion has a transfer paragraph, but it arrives only at the very end.

**Why**: Transfer is best when it occurs *during* learning, not only in the summary. Consider adding a brief transfer sentence in L06's conclusion: "In paper math, you would write: |A x B| = |A| * |B|. The Lean version says `Fintype.card (A x B) = Fintype.card A * Fintype.card B`. Same principle, different notation." This costs one sentence and connects the formalism to familiar math at the point where the multiplication principle is taught.

**Where**: L06 conclusion.

**Effort**: Low (one sentence).

**Recommend**: Yes.

---

### 10. Boss level (L08) is nearly identical to L06

**What**: L06 proves `Fintype.card (Fin 2 x Fin 3) = 6`. L08 proves `Fintype.card (Fin 2 x Bool) = 4`. The proof structure is identical: `rw [Fintype.card_prod]`, then rewrite the factors. The only difference is that L08 uses `Fintype.card_bool` instead of a second `Fintype.card_fin`.

**Why**: A boss level should integrate the world's lessons in a way that requires the learner to make choices, not just replay a pattern with one substituted lemma. The learner who solved L06 can solve L08 mechanically. Consider a boss that requires more integration: for example, `Fintype.card (Fin 2 x Bool) = Fintype.card (Fin 4)` (requires the product decomposition *and* recognizing that both sides equal 4, but stated as an equality between two type-level cardinalities rather than a cardinality-equals-number). Or a multi-component goal involving `Finset.univ`, `Finset.mem_univ`, and `Fintype.card` together.

**Where**: L08.

**Effort**: Medium (redesign the boss goal).

**Recommend**: Consider.

---

## Overall impression

The world has a clean, logical progression: definition (L01), universality (L02), counting bridge (L03-L04), beyond-Fin instances (L05-L06), counterexample (L07), boss (L08). The introductions and conclusions are well-written, with genuine pedagogical narration rather than dry API documentation. The `DecidableEq` analogy in L07 is a nice connection to prior worlds.

The single most important improvement is **adding `NewTheorem` / `TheoremDoc` declarations for `Fintype.card_fin` and `Fintype.card_prod`** (suggestion 1). These are the two most-used lemmas in the world and they are invisible in the learner's inventory. Closely following is **adding `simp` to the disabled tactic set** (suggestion 2) and **adding `DefinitionDoc` for `Fintype.card`** (suggestion 6) -- together, these three items would eliminate the major exploit path and ensure the learner's inventory accurately reflects what was taught.
