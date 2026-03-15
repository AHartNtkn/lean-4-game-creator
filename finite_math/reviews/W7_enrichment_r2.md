# W7 FinsetOperations — Enrichment Review (Round 2)

**Reviewer**: enrichment-reviewer (R2, fresh context)
**World**: FinsetOperations (10 levels: L01–L10)
**R1 changes applied**: `NewTactic tauto` + `TacticDoc tauto` added to L09. L07 already explains `⊆` unfolding.

---

## Ranked suggestions

### 1. `tauto` is introduced in L09 but never used by the learner

**What**: `tauto` is declared as `NewTactic` with a `TacticDoc` in L09 (Distributivity), but L09's proof script does not use `tauto`, and neither does L10. The learner receives the tactic but has zero opportunity to use it or see it used.

**Why**: Introducing a tactic that the learner never practices is a dead inventory item. `tauto` is precisely the tactic that could simplify the propositional reasoning in L09 or L10 after the membership lemmas have been rewritten away. If the intention is to introduce `tauto` as a tool for set-algebraic identities, the learner should see it used — either in the proof itself (e.g., as an alternative closing step after `simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]` has reduced the goal to a propositional tautology) or in a hint that says "alternatively, after rewriting all membership, `tauto` can close the remaining logic." Without this, the learner will not understand what `tauto` does or when to reach for it.

**Where**: L09 (add an alternative hint showing `ext a; simp [Finset.mem_union, Finset.mem_inter]; tauto`) and/or L10 (same pattern for De Morgan).

**Effort**: Medium — add alternative-solution hints to L09 and L10 showing the `simp` + `tauto` shortcut.

**Recommend**: Yes

---

### 2. No `Finset.subset_iff` or `Finset.Subset` theorem declaration in L07

**What**: L07 teaches subset proofs and explains that `s ⊆ t` unfolds to `∀ a, a ∈ s → a ∈ t`. It references `Finset.subset_iff` in the introduction. But there is no `NewTheorem Finset.subset_iff` or `TheoremDoc` for it.

**Why**: The learner's inventory panel will not show `subset_iff` as an available theorem after completing L07. If a later world expects the learner to know this lemma by name (e.g., W8 or the example world), the inventory chain is broken. Even if `⊆` unfolds automatically, having the named lemma in inventory helps learners who want to `rw [Finset.subset_iff]` explicitly.

**Where**: L07 — add `NewTheorem Finset.subset_iff` and a `TheoremDoc`.

**Effort**: Low

**Recommend**: Yes

---

### 3. L05 and L06 are structurally identical — L06 could teach something new

**What**: L05 proves `s ∪ t = t ∪ s` via `ext`, and L06 proves `s ∩ t = t ∩ s` via `ext`. Both follow the exact same proof skeleton: `ext a; constructor; intro h; rw [mem_*] at h; rcases; rw [mem_*]; exact/right/left`.

**Why**: The L06 introduction says "let's practice the `ext` proof pattern on a different operation," which is fine as a consolidation level. But the level also introduces the angle-bracket syntax for destructuring and rebuilding conjunctions — `rcases h with ⟨hs, ht⟩` and `exact ⟨ht, hs⟩` — which is genuinely new. This new skill is somewhat buried in a level that feels like pure repetition. A more enriching alternative: L06 could prove something slightly more interesting, like `s ∩ (s ∪ t) = s` (absorption), which still uses `ext` + `mem_inter` + `mem_union` but requires a different proof structure (one direction needs `constructor` with one part being trivial from the hypothesis, the other requiring `left`). This would give the learner a non-symmetric `ext` proof to contrast with the symmetric commutativity proofs.

**Where**: L06 — consider changing the statement to `s ∩ (s ∪ t) = s` (absorption law) while keeping the angle-bracket syntax teaching.

**Effort**: High (rewrite L06's statement, proof, hints, and conclusion)

**Recommend**: Consider — the current L06 works as consolidation, and absorption could be a good enrichment, but the commutativity-as-practice approach is defensible.

---

### 4. L08 introduction contains visible self-revision ("Wait -- let's make this level actually use `by_cases`")

**What**: The L08 introduction contains the text: "Actually, for this level you do NOT need `by_cases` -- this is a warm-up. But the next level will use it. Wait -- let's make this level actually use `by_cases`. Here is a better task:" This reads as author's internal monologue left in the final text.

**Why**: This is distracting for the learner. The introduction should present the task directly, not narrate the author's design process. The learner doesn't need to know that the author considered a different task first.

**Where**: L08 introduction — remove the "Actually..." through "Wait --" paragraph, and present the `s ⊆ (s \ t) ∪ t` task directly.

**Effort**: Low (text edit only)

**Recommend**: Yes

---

### 5. The "membership triple" proof pattern is used repeatedly but never named

**What**: Levels L01–L04 all follow the same pattern: (1) rewrite with a `mem_*` lemma, (2) handle the resulting logical connective, (3) close concrete membership with `simp`. This pattern is articulated in L04's conclusion but never given a name.

**Why**: Naming proof patterns aids retention and transfer. A learner who can say "I need the membership-rewrite pattern" has a mental hook for the strategy. The L04 conclusion describes the "outermost operation first" rule well, but calling it something concrete (e.g., "the membership-chase pattern" or "peel-and-prove") would help the learner recall it in L09 and L10 when the proof is longer. This also sets up transfer language: in ordinary math, this is called "element-chasing."

**Where**: L04 conclusion — name the pattern. Optionally reference the name in L09 and L10 introductions.

**Effort**: Low (a sentence or two)

**Recommend**: Consider

---

### 6. No level exercises the reverse direction of `mem_union`/`mem_inter`/`mem_sdiff` (from logic to membership)

**What**: L01–L03 all rewrite goals from membership form into logical form (`rw [Finset.mem_*]`). But the reverse direction — starting with logical facts and proving membership — only appears implicitly inside the `ext` proofs of L05–L10 (where you rewrite the goal with `mem_*` and then `exact` the pieces). There is no level where the learner starts with `h : a ∈ s ∨ a ∈ t` and must prove `a ∈ s ∪ t`.

**Why**: In the `ext` proofs, the learner must use the membership lemmas in both directions: hypothesis → logic (forward direction of the biconditional) and logic → membership (reverse direction). But the transition happens inside a larger proof where many things are happening at once. An explicit level where the learner uses `rw [Finset.mem_union]` on a goal (rather than a hypothesis) before the `ext` levels would make L05 less overwhelming.

**Where**: Between L04 and L05 — a new level: "Given `ha : a ∈ s`, prove `a ∈ s ∪ t`." This is a single `rw + left + exact` proof but isolates the goal-direction rewrite.

**Effort**: High (new level, renumbering)

**Recommend**: Consider — L07 (subset) does cover goal-direction rewriting, but it comes after `ext`, which means the learner first encounters goal-direction rewriting inside the complex L05 proof.

---

### 7. L10 conclusion mentions `ext + simp` but the proof doesn't use `simp`

**What**: The transfer moment in the plan says "This is De Morgan's law for finite sets. In ordinary math, you'd prove it by taking an arbitrary element and chasing membership. That's exactly what `ext` + `simp` does." The L10 conclusion references the paper proof but does not mention the `ext` + `simp` shortcut. Meanwhile, L09 introduced `tauto` (per the R1 fix), suggesting the intent is to show the automated approach.

**Why**: The transfer moment from the plan is a good idea that was partially lost in implementation. Adding a line to L10's conclusion — or even a final hidden hint — showing that `ext a; simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto` can close the boss in one shot would make the learner appreciate both (a) the manual proof they just wrote and (b) the power of automation when the membership lemmas are known. This ties together the entire world: you learned the lemmas one by one, and now `simp` can deploy them all at once.

**Where**: L10 conclusion — add a paragraph showing the `simp + tauto` alternative and connecting to the plan's transfer moment.

**Effort**: Low (text addition to conclusion)

**Recommend**: Yes

---

### 8. L03's conclusion summary table is excellent — L01 and L02 would benefit from building toward it

**What**: L03's conclusion has a summary table of all three operations with their logical forms. This is a great reference. But L01 and L02 have no foreshadowing that such a table is coming — they treat each operation in isolation.

**Why**: If L01's conclusion said "We'll see two more operations — intersection and set difference — that follow the same pattern but with different logical connectives," the learner would be primed to look for the pattern. And L02's conclusion could say "That's two of three — union gives `∨`, intersection gives `∧`. One more to go." This builds narrative momentum toward the summary table in L03.

**Where**: L01 conclusion, L02 conclusion — one sentence each.

**Effort**: Low

**Recommend**: Consider

---

### 9. `Finset.ext_iff` is mentioned in L05's introduction but never declared as `NewTheorem`

**What**: L05 introduces the extensionality principle and cites `Finset.ext_iff : s = t ↔ ∀ a, a ∈ s ↔ a ∈ t` in the introduction. But no `NewTheorem Finset.ext_iff` or `TheoremDoc` is declared. Only `ext` the tactic is declared.

**Why**: A learner who wants to use `rw [Finset.ext_iff]` instead of the `ext` tactic (a perfectly valid alternative approach) won't find it in their inventory. Declaring both the tactic and the theorem gives the learner a choice and makes the connection between the tactic and the underlying lemma explicit.

**Where**: L05 — add `NewTheorem Finset.ext_iff` and `TheoremDoc`.

**Effort**: Low

**Recommend**: Consider — the `ext` tactic is the intended tool and `Finset.ext_iff` might encourage less clean proofs. But inventory completeness argues for including it.

---

## Overall impression

The world has a clean, logical progression: three membership lemmas (L01–L03), a combining exercise (L04), `ext` introduced and practiced (L05–L06), subset proofs (L07), case analysis (L08), and two integration proofs (L09–L10 boss). The conclusions are consistently strong, with transfer-to-paper-math paragraphs and clear summaries. The L03 summary table is a highlight. The proof scripts are well-hinted with both open and hidden hints at every decision point.

The single most important improvement is **suggestion 1**: `tauto` is introduced but never used, which means the learner receives a dead tactic. Either add hints showing `tauto` in action (after `simp` reduces to propositional logic) in L09/L10, or remove the `NewTactic tauto` and defer it to a later world. The second priority is **suggestion 4**: the visible self-revision in L08's introduction is a polish issue that should be fixed immediately.
