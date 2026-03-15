# W8 FinsetTransformations -- Playtest Audit R2

**World**: FinsetTransformations (W8)
**Role**: Lecture (8 levels)
**Topic**: `Finset.filter`, `Finset.image`, `Finset.map`, composing filter/image, cardinality under image
**Predecessor**: W7 FinsetOperations (10 levels)

---

## R1 Disposition

| # | R1 issue | Status in R2 |
|---|----------|-------------|
| 1 | `simp` closes 6/8 levels (P0) | **UNCHANGED.** `simp` is still not in DisabledTactic on any level. Confirmed systemic -- deferred per project memory ("Fix after all worlds reviewed"). Downgrading to P2 (systemic/deferred) for this audit. |
| 2 | `norm_num` closes 6/8 levels (P0) | **UNCHANGED.** Same disposition as `simp` -- systemic. |
| 3 | `rcases ... with rfl` untaught in boss (P0) | **PARTIALLY MITIGATED.** The pattern was not isolated before the boss, but investigation shows the FinsetMembership world (W6, predecessor) teaches `rcases h with rfl \| h` in L08/L09. The `rfl`-as-substitution mechanism is the same; only the syntactic position differs (inside angle brackets for existential vs. as disjunction branch). Downgrading from P0 to P1. |
| 4 | L07 is a trivial one-liner (P1) | **UNCHANGED.** L07 is still `exact Finset.card_image_le`. |
| 5 | `simp only [...] at hmem` untaught in boss (P1) | **UNCHANGED.** The boss still uses `simp only [Finset.mem_insert, Finset.mem_singleton] at hmem` which the learner has not practiced. |
| 6 | `Finset.map` introduced but never practiced (P2) | **UNCHANGED.** L05 is still membership-only. `card_map` is never used. |
| 7 | No image non-membership level (P2) | **UNCHANGED.** |
| 8 | `Finset.card_image_of_injective` in inventory but unused (P2) | **UNCHANGED.** |

**Changes since R1**:
- L08 boss now includes cardinality conjunct (`card_image_le`). VERIFIED: the statement has `... \and ... .card <= ... .card`. This is a structural improvement -- the boss now tests both membership reasoning and cardinality reasoning.
- L05 now uses standard mathlib embedding `Nat.succ, Nat.succ_injective`. VERIFIED: cleaner than a hand-rolled proof.
- Build passes (8177 jobs, zero errors).

---

## 1. Overall Verdict

**CONDITIONAL PASS.** The world compiles, teaches filter/image/map membership at appropriate granularity, and the boss genuinely integrates both membership and cardinality reasoning. The R1 blocking issues have been partially addressed or are confirmed systemic (deferred). Two significant issues remain: (a) the `simp` exploitability affects L01-L07 but is a project-wide issue being handled separately, and (b) L07 is still a pedagogically empty one-liner. If the systemic `simp` fix is committed to, and L07 is accepted as-is (with the understanding that its value is primarily in the intro/conclusion text rather than the proof), the world is shippable.

**Blocking issues remaining: 0** (previous P0s downgraded -- `simp` to systemic/deferred, `rcases rfl` to P1 with prior-world mitigation).

---

## 2. Rubric Scores

| Category | R1 | R2 | Notes |
|----------|----|----|-------|
| 1. Coverage closure | 3 | 3 | Filter/image membership: full closure (I/S/R/G). Map: intro-only. Cardinality: passive (read-only in intro text, one-liner proofs). |
| 2. Granularity fit | 2 | 2 | L07 is still overfine (one-liner). L05 is mildly overfine (proof identical to L03). All others well-scoped. |
| 3. Proof-move teaching | 2 | 3 | Filter conjunction: well taught (L01-L02). Image existential + witness: well taught (L03-L04). `rcases ... rfl` in boss: still first-contact in angle-bracket form but prior-world seeding exists for the `rfl`-substitution concept. Upgraded from 2 to 3. |
| 4. Inventory design | 3 | 3 | Good doc entries for `mem_filter`, `mem_image`, `mem_map`, `card_image_le`, `card_map`, `filter`, `image`, `map`. `card_image_of_injective` still phantom. |
| 5. Hint design | 2 | 2 | Layered strategy-then-code in L01-L06. Boss still has the `simp only ... at hmem` untaught pattern. No Branch alternatives anywhere. |
| 6. Progression | 2 | 3 | Boss now integrates cardinality (Part B) in addition to membership (Part A). L07-L08 jump still has the `simp only at` surprise, but Part B is now a clean retrieval of L07's `card_image_le`. Upgraded. |
| 7. Mathematical authenticity | 3 | 3 | Good filter/image contrast. Cardinality discussion honest. Transfer moment in L08 conclusion. |
| 8. Paper-proof transfer | 3 | 3 | L08 conclusion explicitly writes the paper proof. |
| 9. Technical fit | 2 | 2 | Compiles. `simp` exploit systemic. Missing TacticDoc warnings for `native_decide`, `aesop`, `simp_all` in build output (pre-existing from earlier worlds). |

**Average: 2.67.** Below the 3.0 threshold but approaching it. One category (granularity) is at 2 due to L07.

---

## 3. Coverage Gaps

### 3a. Covered well
- `Finset.filter` definition and membership: I (L01), S (L02), R (L06), G (L08). Full closure.
- `Finset.mem_filter`: I (L01), S (L02), R (L06), G (L08). Full closure.
- `Finset.image` definition and membership: I (L03), S (L04), R (L06), G (L08). Full closure.
- `Finset.mem_image`: I (L03), S (L04), R (L06), G (L08). Full closure.
- `use` for existential witnesses: R across L03-L06 (taught in prior worlds). Good retrieval.
- "Outside-in" composition strategy: I+S (L06), G (L08). Good.
- `Finset.card_image_le`: I (L07), G (L08 Part B). Adequate but shallow.

### 3b. Remaining gaps
| Gap | Severity | Notes |
|-----|----------|-------|
| `Finset.map` has no practice/retrieval after L05 | P2 | Introduced then never reused. `card_map` never exercised. Acceptable if the world's role is "introduce map, use it later." |
| `rcases ... with rfl` inside angle brackets (existential form) | P1 | Never isolated before boss. The disjunction form (`rfl \| h`) was taught in W6 L08. Same mechanism, different syntax. |
| `simp only ... at h` (localized simp with hypothesis targets) | P1 | Used in L08 boss but never previously practiced in this world or its predecessors in this exact form. |
| Concrete non-membership in image | P2 | L02 covers filter non-membership. Image non-membership never covered. |
| `card_image_of_injective` phantom inventory item | P2 | In `NewTheorem` but never used. |

---

## 4. Granularity Defects

| Level | Defect | Severity | Notes |
|-------|--------|----------|-------|
| L07 | **Overfine**: Proof is `exact Finset.card_image_le`. No proof move taught. Teaching value is entirely in the intro/conclusion text. | P1 | Same as R1. The enrichment reviewer has flagged this twice. The level's existence is justified only as a "definitional exposure" moment. If accepted, acknowledge it as a text-heavy, proof-light level. |
| L05 | Mildly overfine: Proof shape identical to L03. Differentiation from `image` is entirely textual. | P2 | Improved slightly with standard embedding. Still a concern. |

---

## 5. Statement Exploitability

### Confirmed: `simp` closes L01-L07 (systemic, deferred)

Verified by compilation test: plain `simp` (no arguments) closes all of L01, L02, L03, L04, L05, L06, and L07. `norm_num` also closes L01-L05 and L07. These are fully confirmed from R1.

**L08 boss is NOT exploitable by `simp`.** Verified: `simp` alone fails on the full conjunction. `simp [Finset.mem_image, Finset.mem_filter]` also fails. The boss requires genuine manual work (intro, rcases, rw, constructor steps) before automation can close individual subgoals. This is good.

### L08 Boss exploit analysis (new for R2)

Tested multiple exploit paths:
- `simp` alone: FAILS (good)
- `norm_num [...]`: FAILS (good)
- `constructor; intro x hx; simp_all [...]`: FAILS (good, but `simp_all` is disabled)
- `constructor; intro x hx; simp only [...] at *; obtain ...; omega` + `exact Finset.card_image_le`: WORKS but requires 6+ manual steps (acceptable -- this IS the intended proof shape)
- `decide`: WOULD CLOSE but is disabled (good)

**Boss verdict**: Not exploitable with available tactics. The conjunction of membership reasoning (Part A) and cardinality (Part B) provides genuine integration challenge. Part A requires understanding image existentials and filter conjunctions; Part B requires knowing `card_image_le`.

### `rfl` on cardinality (pre-existing, accepted)

As noted in R1 and project memory: `Fintype.card (Fin n x Fin m) = n*m` is definitionally true and `rfl` closes it. Cannot disable `rfl`. Accepted as P2.

---

## 6. Interactive Proof Quality

| Level | Quality | Notes |
|-------|---------|-------|
| L01 | Good | Each step (`rw`, `constructor`, `simp [...]`, `rfl`) gives visible feedback. |
| L02 | Good | `rw`, `intro`, `rcases`, `norm_num at hp` -- each step changes the goal visibly. |
| L03 | Good | `rw`, `use`, `constructor`, `simp [...]`, `rfl` -- clear step-by-step. |
| L04 | Good | Same pattern as L03 with harder witness. |
| L05 | Good | Same pattern as L03. |
| L06 | Good | Nested unpacking with visible intermediate states. The "outside-in" strategy plays out interactively. |
| L07 | Trivial | One step, no interaction. P2 (see granularity). |
| L08 Part A | Mostly good | Each step (intro, rw at hx, rcases, rw at ha, rcases, rw, constructor) gives feedback. The `simp only [...] at hmem` step is complex but produces a visible simplification. |
| L08 Part B | Trivial | One step (`exact Finset.card_image_le`). Acceptable as Part B of a boss -- the complexity is in Part A. |

**No red flags**: No elaborate one-liners, no opaque goals, no steps requiring multi-line expressions before feedback.

---

## 7. Learner Simulation

### Attentive novice

**L01-L02** (filter membership): Smooth entry and natural progression (positive then negative direction). The novice learns `mem_filter` by doing.

**L03-L04** (image membership): Clear introduction of the existential pattern. The witness choice in L04 requires a moment of arithmetic thought. Good.

**L05** (map): The novice reads about `map` vs `image`, does an identical proof, and walks away knowing `map` exists but unsure when they'd use it. The text does the teaching, not the proof. Acceptable for definitional exposure.

**L06** (composition): **First genuine challenge.** The novice must decide which membership lemma to apply first. The "outside-in" strategy is introduced here. Hints guide well. Good integration of L01+L03 skills.

**L07** (cardinality): **Likely stuck point**: The novice may try to compute both sides manually (which would be educational) but the hint immediately gives `exact Finset.card_image_le`. The novice types one line and moves on. The conclusion text discusses the interesting math (strict inequality, injectivity). The novice learns from reading, not proving.

**L08** (boss):
- **First stuck point**: After `rw [Finset.mem_image] at hx`, the novice sees `hx : exists a, a in filter (. > 3) {1,...,5} and a + 1 = x`. The hint says to use `rcases hx with (a, ha, rfl)`. The novice has seen `rcases h with rfl | h` in W6 but not inside angle brackets for an existential. The hint explains the `rfl` behavior. The novice can follow the hint but may not fully understand why `rfl` works here vs. the disjunction case.
- **Second stuck point**: `simp only [Finset.mem_insert, Finset.mem_singleton] at hmem` requires typing a multi-target simp call. The novice may try `simp at hmem` (which would work if simp is enabled) or `rw [Finset.mem_insert] at hmem` (which would also work but require more steps).
- **Rescue quality**: Hidden hints give exact tactic calls. Recovery is possible but hint-dependent for novel patterns.
- **Overall**: The novice can complete the boss with hints. Without hints, stuck at the `rcases rfl` step if they haven't internalized the W6 pattern in this new context.

### Experienced Lean user

**L01-L07**: An experienced user can currently `simp` through all 7 levels (systemic issue). If `simp` were disabled, the experienced user would find L01-L06 reasonably paced and L07 trivial.

**L08**: Requires genuine work. The experienced user would likely use `simp only [...] at *` followed by `omega`, which is close to the intended solution. `decide` is blocked. Good.

**Alias gaps**: None. `mem_filter`, `mem_image`, `mem_map` are consistently used.

**Inventory clutter**: `card_image_of_injective` is unused inventory. Mild clutter.

**Friction**: L05's proof being identical to L03 is avoidable friction for an experienced user who sees the pattern immediately. The text in the intro/conclusion does the differentiating work.

---

## 8. Boss Integrity (L08)

| Check | Status | Notes |
|-------|--------|-------|
| Seeded subskills | GOOD | `mem_filter` (L01-L02 full closure), `mem_image` (L03-L04 full closure), `rcases` (W6 L08 for rfl pattern), `use` (prior worlds), `constructor` (W1), `omega` (W1), `card_image_le` (L07). |
| Closure quality | GOOD | Both `mem_filter` and `mem_image` have I/S/R coverage before the boss uses them in integration. |
| Integration quality | GOOD | The boss is NOT a gauntlet. Part A requires combining filter and image reasoning in a single proof chain (not just replaying L01 then L03 in sequence). The `rfl` substitution creates a genuine planning challenge. Part B adds cardinality. |
| Surprise burden | MODERATE | Two items: (1) `rcases ... with rfl` in existential form -- mitigated by W6 seeding of the concept. (2) `simp only [...] at hmem` -- untaught in this specific form. Both have hidden hints for rescue. |
| Cardinality conjunct | NEW/GOOD | Part B (`card_image_le`) was added since R1. It provides genuine two-dimensional integration (membership + cardinality). Part B is a clean retrieval of L07. |
| Can the learner explain the proof in words? | YES | The conclusion writes the paper proof explicitly. The Lean proof structure mirrors the mathematical argument. |

**Boss verdict**: The boss is well-designed. It genuinely integrates the world's repertoire across two dimensions (membership reasoning in Part A, cardinality reasoning in Part B). The `rfl` substitution in `rcases` creates a planning challenge beyond replaying individual levels. The surprise burden from R1 has been partially mitigated by confirming W6 seeding of the `rfl`-in-rcases concept. The remaining surprise (`simp only at hmem`) is P1 but not blocking -- the hint gives the exact command and the step is natural for anyone who knows `simp`.

---

## 9. Course-Role Sanity

The world is a **lecture** world and behaves as one:
- L01, L03, L05: First-contact levels (filter, image, map).
- L02, L04: Supported practice (negative direction for filter, harder witness for image).
- L06: Integration (composition).
- L07: Definitional exposure (cardinality bound).
- L08: Boss.

**Misfits**:
- L07 functions as a text-delivery vehicle rather than a level. Its pedagogical value is in the intro/conclusion, not the proof. This is borderline acceptable for a "definitional exposure" level, but it means the learner never *does* cardinality reasoning before the boss asks for it.

---

## 10. Technical Risks

| Risk | Severity | Details |
|------|----------|---------|
| `simp` not disabled | P2 (systemic/deferred) | Closes L01-L07. Being tracked project-wide per memory notes. |
| `norm_num` not disabled | P2 (systemic/deferred) | Closes L01-L05, L07. Same disposition. |
| Missing TacticDoc warnings | P3 | Build warns about `native_decide`, `aesop`, `simp_all` in L08. These TacticDocs exist in earlier worlds (W4 L01) but the build re-warns. Pre-existing, not W8-specific. |
| `card_image_of_injective` phantom | P2 | In `NewTheorem` but never used. Low risk -- the learner sees it in their inventory but isn't expected to use it. |

---

## 11. Ranked Patch List

| # | Severity | Level(s) | Issue | Recommended Fix |
|---|----------|----------|-------|-----------------|
| 1 | P1 | L07 | Overfine: `exact Finset.card_image_le` teaches no proof move | Redesign to require multi-step proof (e.g., prove the image has exactly 2 elements, or prove strict inequality). Alternatively, accept as a text-heavy definitional-exposure level and document this design choice. Both R1 enrichment suggestions #1 and R2 enrichment #1 flagged this. |
| 2 | P1 | L08 | `simp only [...] at hmem` is untaught | Change the boss's intended solution to avoid `simp only ... at hmem`. Alternative: use `rcases hmem with` to destructure the disjunction chain directly, or use individual `rw [Finset.mem_insert] at hmem` steps. This also improves interactive quality by breaking one complex tactic call into multiple simpler ones. |
| 3 | P1 | L08 | `rcases ... with rfl` in existential form not isolated | Mitigated by W6 seeding of `rfl`-in-rcases concept. If addressed: modify L04 to use `rcases` with `rfl` pattern on a simpler image existential, or add a short coaching level before the boss. If not addressed: acceptable with the existing hidden hints. |
| 4 | P2 | L07 | `card_image_of_injective` in NewTheorem but unused | Either add a level using it (natural companion to the L07 redesign in patch #1) or remove from `NewTheorem` and mention only in conclusion text. |
| 5 | P2 | L05 | `map` introduced but differentiation is textual only | Consider adding a `card_map` exercise as a second part of L05 to differentiate from `image` mechanically. |
| 6 | P2 | L08 | Boss conclusion says "from W6/W7" -- should use world names | Change "from W6/W7" to "from the FinsetMembership world" or similar. |
| 7 | P2 | All | `simp` and `norm_num` exploit (systemic) | Deferred to systemic fix pass. No action needed in W8-specific review. |
| 8 | P3 | None | No image non-membership level | Consider for future enrichment. Not blocking. |

---

## 12. What to Playtest After Patching

If patches #1-#3 are implemented:
1. **L07 redesign** -- verify the new version requires genuine reasoning and compiles.
2. **L08 boss** -- verify the solution works without `simp only ... at hmem` (if patch #2 is applied). Verify no new surprise burdens.
3. **L04 (if modified for patch #3)** -- verify the `rcases rfl` pattern is taught cleanly.
4. **Full exploit sweep** -- verify no new one-shot tactic closes any level.

If only patch #6 is applied (text fix):
- No re-audit needed.

If no patches are applied:
- The world is shippable as-is, with the understanding that L07 is a text-delivery level and the `simp` exploit is being tracked systemically.
