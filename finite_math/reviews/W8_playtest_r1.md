# W8 FinsetTransformations -- Playtest Audit R1

**World**: FinsetTransformations (W8)
**Role**: Lecture (8 levels)
**Topic**: `Finset.filter`, `Finset.image`, `Finset.map`, composing filter/image, cardinality under image
**Predecessor**: W7 FinsetOperations (10 levels)

---

## 1. Overall Verdict

**NEEDS REVISION.** The world compiles and teaches the right concepts at the right granularity, but has serious exploitability problems: bare `simp` and `norm_num` close 6 of 8 levels as one-shot tactics. The boss introduces a new proof move (`rcases ... with ⟨a, ha, rfl⟩`) that was never isolated. L07 is a trivial one-liner that teaches no proof move. Hints are generally well-layered but the boss hints include an untaught `simp only ... at hmem ⊢` pattern.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Filter/image/map membership well covered; cardinality coverage thin (one one-liner) |
| 2. Granularity fit | 2 | L07 is overfine (one-liner); most others are well-scoped |
| 3. Proof-move teaching | 2 | Filter membership well taught; image existential well taught; but boss introduces `rfl`-substitution pattern cold |
| 4. Inventory design | 3 | Good doc entries; appropriate NewTheorem/NewDefinition placement |
| 5. Hint design | 2 | Layered strategy-then-code in L01-L06; boss hints include untaught `simp only ... at` pattern; no Branch alternatives |
| 6. Progression (demo→practice→transfer→boss) | 2 | Good for filter (L01→L02) and image (L03→L04); but L07→L08 jump is abrupt; boss has surprise burdens |
| 7. Mathematical authenticity | 3 | Good filter/image contrast; cardinality discussion is conceptually honest; transfer moment in L08 conclusion |
| 8. Paper-proof transfer | 3 | L08 conclusion explicitly writes the paper proof; good |
| 9. Technical fit | 2 | Compiles; but `simp` exploit is a systemic gap |

**Average: 2.4** -- below the 3.0 threshold. Two categories at 2 is a blocking deficiency.

---

## 3. Coverage Gaps

### 3a. Covered well
- `Finset.filter` definition and membership (I in L01, S in L02, R in L06, G in L08)
- `Finset.mem_filter` (I in L01, S in L02, R in L06, G in L08) -- full closure
- `Finset.image` definition and membership (I in L03, S in L04, R in L06, G in L08)
- `Finset.mem_image` (I in L03, S in L04, R in L06, G in L08) -- full closure
- `Finset.map` definition and membership (I in L05) -- introduced but no further practice
- Outside-in composition strategy (I+S in L06, G in L08)
- `use` for existential witnesses (R in L03-L06, from prior worlds)

### 3b. Gaps
| Gap | Severity | Description |
|-----|----------|-------------|
| `Finset.map` has no practice/retrieval after L05 | P2 | Introduced then never used again; no transfer or retrieval |
| `rcases ... with ⟨a, ha, rfl⟩` (rfl-substitution in rcases) | P0 | Used in boss but never isolated/taught. This is a distinct proof move from `rcases ... with ⟨a, ha, heq⟩` |
| `simp only ... at h ⊢` (localized simp with hypothesis) | P1 | Used in boss hints but never taught. The earlier levels use `simp [...]` in goal position only |
| Concrete non-membership in image | P2 | L02 shows non-membership for filter but no level shows non-membership for image (e.g., "7 is NOT in the image of {1,2,3} under doubling") |
| `Finset.card_image_le` has no genuine practice | P1 | Introduced as a one-liner in L07 then never used again |

---

## 4. Granularity Defects

| Level | Defect | Severity | Recommendation |
|-------|--------|----------|----------------|
| L07 | **Overfine**: The proof is literally `exact Finset.card_image_le`. No proof move is taught. The learner types one exact-application and is done. The interesting content is in the conclusion text, not the proof. This is Failure #3 (teaches no reusable move). | P1 | Redesign: make the learner actually compute both sides (e.g., show `(image f s).card = 2` and `s.card = 4` then combine with the general lemma), or replace with a level that requires the learner to prove `card_image_of_injective` by providing an injectivity proof. |
| L05 | Mild overfine risk: The proof shape is identical to L03 (existential witness). The lesson is "map exists and its membership proof is the same as image." The pedagogical value is primarily in the intro/conclusion text, not the proof itself. | P2 | Acceptable if L05's real purpose is definitional exposure. But consider adding a cardinality exercise using `Finset.card_map` to differentiate it from L03. |

---

## 5. Statement Exploitability (1b)

### P0 -- `simp` closes 6/8 levels

Bare `simp` (no arguments) closes L01, L02, L03, L04, L05, and L07. `simp` is not in the DisabledTactic list. Only `simp_all` is disabled.

Additionally, bare `norm_num` (no arguments) closes the same 6 levels. `norm_num` is also not disabled.

**Affected levels**:
| Level | `simp` | `norm_num` | `decide` (disabled) |
|-------|--------|-----------|---------------------|
| L01 | closes | closes | closes (blocked) |
| L02 | closes | closes | closes (blocked) |
| L03 | closes | closes | closes (blocked) |
| L04 | closes | closes | closes (blocked) |
| L05 | closes | closes | closes (blocked) |
| L06 | fails | fails | closes (blocked) |
| L07 | closes | closes | closes (blocked) |
| L08 | fails | fails | closes (blocked) |

**Impact**: A learner who discovers `simp` can skip 6 of 8 levels without learning filter, image, or map reasoning. The DisabledTactic list blocks `decide` (which closes all 8) but leaves `simp` and `norm_num` wide open.

**Fix**: Add `simp` to DisabledTactic on all levels where it bypasses the lesson. The author uses `simp [Finset.mem_insert, Finset.mem_singleton]` in the intended proofs, but this usage can be replaced with explicit `Finset.mem_insert.mpr` or individual `rw` steps, or `simp` can be disabled and the hints adjusted to use other approaches for the membership subgoals.

Alternatively, if `simp` must remain available for the `simp [mem_insert, mem_singleton]` steps, then the statements must be restructured so that `simp` alone (without arguments) does not close the full goal. But given the current concrete finset statements, this is not possible without making the math abstract.

**Recommended fix**: Add `simp` to DisabledTactic on L01-L07 (not L08 where it's only used as `simp only` in a subgoal). For the membership subgoals in the intended proofs, switch to explicit `rw` chains or `Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))` or similar. This is a structural change.

**Also add `norm_num` to DisabledTactic on L01, L03, L04, L05, L07** where it is not needed for the intended solution. Keep `norm_num` available on L02 (where `norm_num at hp` is the intended proof step) and L04 (where `norm_num` closes the equation subgoal). For L04, `norm_num` can remain if `simp` is disabled, since the learner still needs to do the `rw [mem_image]` + `use 2` + `constructor` steps first.

### P2 -- `decide` closes all 8 levels (already blocked)

`decide` closes all 8 levels but is already in DisabledTactic. No action needed.

### P2 -- `rfl` on L01, L03, L05, L06 equation subgoals

After splitting with `constructor`, the equation subgoals (`2 % 2 = 0`, `3 * 2 = 6`, etc.) close with `rfl`. This is fine -- `rfl` is a basic tactic and the learner still needs to do the structural work first. Not an exploit.

---

## 6. Interactive Proof Quality (1c)

| Level | Issue | Severity |
|-------|-------|----------|
| L01 | Good: each step (`rw`, `constructor`, `simp`, `rfl`) gives visible feedback | OK |
| L02 | Good: `rw`, `intro`, `rcases`, `norm_num at` -- each step changes the goal | OK |
| L03 | Good: `rw`, `use`, `constructor`, `simp`, `rfl` | OK |
| L04 | Good: same pattern as L03 | OK |
| L05 | Good: same pattern as L03 | OK |
| L06 | Good: nested unpacking with visible intermediate states | OK |
| L07 | Trivial: one step, no interaction | P2 (see granularity) |
| L08 | `simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢` is a complex multi-location simp call. Requires the learner to type both `at hmem` and `⊢` in a single tactic call before seeing any result. | P1 |

---

## 7. Learner Simulation

### Attentive novice

**L01**: Smooth entry. The intro explains `mem_filter` clearly. `rw [Finset.mem_filter]` → `constructor` → two subgoals. The novice may struggle with the membership subgoal (`2 ∈ {1,2,3,4,5}`), but the hint gives `simp [...]`. If `simp` is disabled (as recommended), a more explicit hint will be needed.

**L02**: Good progression. Non-membership is a natural follow-up. The novice sees `intro h` for negation, `rcases h`, then `norm_num at hp`. The `norm_num at hp` step might feel mysterious (what does "at hp" do?), but the hint explains it.

**L03**: First contact with `mem_image`. The existential is well-motivated. The witness `3` is obvious. Good.

**L04**: Slightly harder witness (`2² + 1 = 5`). The novice needs to compute. Good retrieval exercise.

**L05**: The intro does the heavy lifting. The proof is identical to L03. The novice learns that `map` exists but not why it matters beyond the text. The proof doesn't exercise the `card_map` fact introduced here.

**L06**: This is the first genuine integration level. The novice must think about which membership lemma to use first (outside-in strategy). The hints guide well.

**L07**: **First likely stuck point**: The novice reads the intro, sees `Finset.card_image_le`, and types `exact Finset.card_image_le`. Done. There is no moment of struggle or discovery. The conclusion explains the interesting math (strict inequality, injectivity distinction) but the proof itself taught nothing. **Most likely wrong move**: The novice might try to compute both sides explicitly, which would be more educational but harder.

**L08 (Boss)**:
- **First likely stuck point**: After `rcases hx with ⟨a, ha, rfl⟩`. The `rfl` pattern in `rcases` is new. The novice does not know that `rfl` can be used in a destructuring pattern to substitute. The hint explains it but this is a new proof move being introduced in the boss, not just retrieved.
- **Second stuck point**: `simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢` -- the novice has never used `at` with multiple targets or `simp only`.
- **Rescue quality**: The hidden hints give the exact tactic calls, which is sufficient for recovery but means the boss is being coached rather than tested.

### Experienced Lean user

**L01-L06**: An experienced user would want to use `simp` or `decide` and be frustrated if they're disabled. But `simp` is currently NOT disabled, so the experienced user can skip 6/8 levels. This is the exploitability problem.

**L07**: An experienced user finishes in 1 second. No friction but also no value.

**L08**: An experienced user would use `decide` (blocked) or `simp [Finset.mem_image, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; omega` which currently does NOT close the goal (good). So the boss at least requires manual work even for experts.

**Alias gaps**: None significant. The world uses `Finset.mem_filter`, `Finset.mem_image`, `Finset.mem_map` consistently.

**Inventory clutter**: `Finset.card_image_of_injective` is introduced in L07 but never used. This is mild clutter.

---

## 8. Boss Integrity (L08)

### Required checks:

| Check | Status | Notes |
|-------|--------|-------|
| Seeded subskills | PARTIAL | `mem_filter` (L01-L02), `mem_image` (L03-L04), `rcases` (W7). But `rcases ... rfl` pattern NOT seeded. `simp only ... at h ⊢` NOT seeded. |
| Closure quality | PARTIAL | Filter and image membership have full closure. But the rfl-substitution and simp-only patterns are first-contact in the boss. |
| Integration quality | GOOD | The boss genuinely requires combining filter and image reasoning in a single proof. It is not a gauntlet (concatenation of earlier proofs). |
| Surprise burden | HIGH | Two untaught micro-skills: `rcases ... rfl` and `simp only ... at hmem ⊢`. Both appear in hidden hints but the learner hasn't practiced them. |
| Can the learner explain the proof in words? | YES | The conclusion explicitly writes the paper proof. Good transfer. |

**Boss verdict**: The boss is well-designed structurally (genuine integration, good transfer moment) but has a **lottery element** (Failure #9): the `rcases ... rfl` substitution trick is a new proof move that was never isolated. A learner who hasn't seen this pattern will get stuck and rely on hints, which means the boss is coaching rather than testing.

**Fix**: Add a pre-boss coaching level that isolates the `rcases ⟨a, ha, rfl⟩` pattern on a simpler image membership proof. For example: "Given `h : x ∈ Finset.image (· + 10) {1,2,3}`, prove `x > 5`." This would teach the rfl-substitution pattern before the boss requires it in combination with filter reasoning.

---

## 9. Course-Role Sanity

The world is cast as a **lecture** world and behaves as one: L01, L03, L05 are first-contact levels; L02, L04, L06 are supported practice; L07 is definitional exposure; L08 is boss.

**Misfits**:
- L07 behaves more like a doc entry than a level. It does not exercise any proof move.
- L05 is first-contact for `map` but the proof is identical to L03 (`image`). The definitional distinction between `map` and `image` is taught via text, not via proof.

---

## 10. Technical Risks

| Risk | Severity | Details |
|------|----------|---------|
| Missing TacticDoc warnings in build | P2 | The build shows "Missing Tactic Documentation" for `trivial`, `decide`, `native_decide`, `aesop`, `simp_all` in L08_Boss.lean. These are pre-existing upstream issues (TacticDocs defined in earlier worlds but the build re-warns). Not new to W8. |
| `simp` not disabled | P0 | Systemic exploitability. See Section 5. |
| `norm_num` not disabled | P0 | Systemic exploitability on 6/8 levels. See Section 5. |
| No NewTactic declarations | P2 | No tactics are newly introduced in this world (filter/image/map are theorems/definitions, not tactics). The world uses `rcases`, `use`, `rw`, `constructor`, `intro`, `exact`, `norm_num`, `simp`, `omega` -- all taught previously. This is fine. |

---

## 11. Ranked Patch List

| # | Severity | Level(s) | Issue | Recommended Fix |
|---|----------|----------|-------|-----------------|
| 1 | P0 | L01-L05, L07 | `simp` closes entire goals | Add `simp` to DisabledTactic on L01-L07. Rework membership subgoals in intended proofs to use explicit `rw` steps or `Finset.mem_insert.mpr`/`Finset.mem_singleton.mpr`. |
| 2 | P0 | L01, L03-L05, L07 | `norm_num` closes entire goals | Add `norm_num` to DisabledTactic on L01, L03, L05, L07 (where it's not needed in intended proof). Keep on L02 (`norm_num at hp`) and L04 (`norm_num` for equation subgoal). |
| 3 | P0 | L08 (Boss) | `rcases ... with ⟨a, ha, rfl⟩` is untaught | Add a pre-boss coaching level (new L07.5 or renumber) that isolates the rfl-substitution pattern in rcases on a simple image problem. |
| 4 | P1 | L07 | Overfine: one-liner `exact` with no proof move | Redesign to require multi-step proof. E.g., prove `(Finset.image (· % 2) {0,1,2,3}).card < {0,1,2,3}.card` using `card_image_le` plus a concrete computation showing the image has only 2 elements. Or combine with the coaching level from patch #3. |
| 5 | P1 | L08 (Boss) | `simp only [...] at hmem ⊢` is untaught | Either teach `simp only` with `at` locators in a prior level, or change the boss solution to avoid it (e.g., use explicit `rw` steps or `rcases hmem with ...` pattern to destructure the disjunction in hmem). |
| 6 | P2 | L05 | `Finset.map` introduced but never practiced/retrieved | Consider adding a follow-up level using `card_map` to differentiate `map` from `image`. If not, at least note in PLAN that `map` coverage is intro-only in W8. |
| 7 | P2 | All | No image non-membership level | Consider adding a level showing `7 ∉ Finset.image (· * 2) {1,2,3}` to parallel L02's filter non-membership. This would exercise `∀ a ∈ s, f a ≠ 7` reasoning. |
| 8 | P2 | L07 | `Finset.card_image_of_injective` introduced but never used | Either add a level that uses it or remove it from NewTheorem to reduce clutter. |

---

## 12. What to Playtest After Patching

After implementing the patches above, re-audit:

1. **All levels for exploitability** -- verify that `simp`, `norm_num`, and any other one-shot tactics are properly gated after DisabledTactic changes.
2. **The new coaching level** (if added for `rcases ... rfl`) -- verify it teaches the rfl-substitution pattern clearly and has proper hints.
3. **L08 Boss** -- verify no surprise burdens remain after the coaching level is added and `simp only` is either taught or removed from the solution.
4. **L07 redesign** -- verify the new version teaches a genuine proof move and is not still a one-liner.
5. **Intended proofs still work** -- after adding `simp` to DisabledTactic, verify that the intended proofs compile (they may need adjustments where `simp [mem_insert, mem_singleton]` was used).
