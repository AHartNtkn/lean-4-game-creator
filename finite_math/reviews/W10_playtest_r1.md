# W10 FinsetInduction — Playtest Audit R1

**World**: FinsetInduction (9 levels, Lecture)
**World promise**: The learner can use `Finset.induction_on` as an induction principle distinct from `Nat.induction`, and can prove cardinality results by induction on finsets.
**Build**: Compiles. Build warnings present (see Technical Risks).
**Date**: 2025-03-15

---

## 1. Overall Verdict

**NEEDS REVISION.** The world has a coherent pedagogical arc and strong mathematical authenticity, but multiple P0 and P1 defects undermine it. The most critical: `simp` is not disabled in 8 of 9 levels, and it closes L01 (the induction warm-up) entirely, bypassing the lesson. L06 is exploitable by `norm_num` and `simp` (both not disabled), making the `card_le_card` lesson skippable. There is an orphan file (`L05_CardinalityByInduction.lean`) that is not imported but still present on disk, and a plan drift where the actual L05 (CardInsertLe, using `by_cases`) diverges from the plan's L05 (cardinality-by-induction). Missing `NewTactic` declarations for `induction`, `absurd`, and `case` produce build warnings. `Finset.insert_union` is introduced in the wrong level (L05 instead of L09).

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Core items tracked; V4/L8/V15 covered. Plan drift on L05. |
| 2. Granularity fit | 3 | Each level has a clear dominant lesson. L05 plan drift is a concern. |
| 3. Proof-move teaching | 3 | Induction pattern, contradiction pattern, vacuous truth all taught well. |
| 4. Inventory design | 2 | `insert_union` misplaced in L05. No `NewTactic` for `induction`/`absurd`/`case`. Missing `TheoremDoc` for `card_union_le`. |
| 5. Hint design | 3 | Layered hints present. Strategy-first, code-hidden pattern followed. |
| 6. Progression | 3 | Review → intro → practice → comparison → boss arc is solid. |
| 7. Mathematical authenticity | 4 | Transfer moments in conclusions. Good "in plain language" sections. |
| 8. Paper-proof transfer | 3 | Good transfer moments in L02 conclusion table and L09 conclusion. |
| 9. Technical fit | 2 | Orphan file, `simp` exploit, missing docs, build warnings. |

**Average: 2.9** (below the 3.0 threshold; blocked by red flags)

**Red flags triggered:**
- Exploitable statements (L01 via `simp`, L06 via `simp`/`norm_num`)
- Missing docs for disabled theorems (`card_union_le`)
- Build warnings for undeclared tactics

---

## 3. Statement Exploitability (1b)

### P0 (blocking) exploits

| Level | Exploit | Tactic | Effect |
|-------|---------|--------|--------|
| **L01** | `simp` closes `0 + n = n` | `simp` (not disabled) | Bypasses entire Nat induction lesson |
| **L06** | `simp` or `norm_num` closes `{1,2}.card ≤ {1,2,3}.card` | `simp`, `norm_num` (neither disabled) | Bypasses `card_le_card` lesson entirely; `h` is unused |

### P1 (high) exploits

| Level | Exploit | Tactic | Effect |
|-------|---------|--------|--------|
| **L02** | `simp [Finset.eq_empty_or_nonempty]` closes goal | `simp` with disabled theorem as explicit arg | In game, explicit arg with disabled theorem is blocked, but player might discover other simp lemma combos. Severity: P1 because partial mitigation exists. |
| **L03** | `simp at h; exact h` converts `h : s.card = 0` to `h : s = ∅` | `simp` at hypothesis | Bypasses induction; simp internally uses `card_eq_zero` as a default simp lemma |
| **L05** | `simp [Finset.card_insert_le]` closes goal | `simp` with disabled theorem | Blocked by game if player names the theorem, but `card_insert_le` may be a default simp lemma |
| **L08** | `simp [Finset.eq_empty_or_nonempty]` closes goal | `simp` with disabled theorem | Same as L02 — partial mitigation |

### P2 (medium) exploits

| Level | Exploit | Notes |
|-------|---------|-------|
| **L04** | `exact h.card_pos` (dot notation on disabled theorem) | `Finset.Nonempty.card_pos` is disabled; dot notation may bypass |
| **L09** | `simp [Finset.card_union_le]` | Disabled theorem as explicit arg — blocked in game |

### Fix for P0 exploits

**Add `simp` to `DisabledTactic` in L01, L02, L03, L04, L05, L06, L08, L09.** L07 already disables `simp`. Also add `norm_num` to L06's `DisabledTactic`.

Standard disabled set should be: `trivial decide native_decide aesop simp_all simp`

---

## 4. Coverage Gaps

### Missing coverage items

1. **`induction` tactic (NewTactic)**: The `induction` tactic is the central tool of this world but has no `NewTactic` declaration anywhere in the course. Build warns about this. Should be declared in L01 or L02 with a `TacticDoc`.

2. **`absurd` (NewTactic/NewTheorem)**: Used in L04 and mentioned in hints. No `NewTactic` or `TacticDoc`. Build warns.

3. **`case` syntax (NewTactic)**: Used in every induction proof (`case empty =>`, `case insert a s' ha ih =>`). No `NewTactic`. Build warns.

4. **`Finset.mem_range` (NewTheorem)**: Used in L07's proof but never declared via `NewTheorem` in any world. Build warns.

5. **Plan drift on L05**: The plan specifies "A cardinality-by-induction proof" (V4 (S), M9 (R)) but actual L05 is `CardInsertLe` using `by_cases`. This means V4 gets one fewer supported practice level than planned. The orphan file `L05_CardinalityByInduction.lean` matches the plan but is not imported.

### Coverage items present

- V3 (review): L01 — Nat induction review. Good.
- V4 (I): L02 — Finset.induction_on introduction. Good.
- V4 (S): L03, L04 — Supported practice. Good (but plan expected L05 too).
- V15 (I): L06 — card_le_card. Good.
- V4 (R): L07 — Comparison of induction principles. Good.
- L17 (S): L08 — refine usage. Good.
- V4 (G), L8 (G): L09 — Boss integrates. Good.

---

## 5. Granularity Defects

### 5a. Level-level issues

1. **L05 (CardInsertLe) — plan mismatch**: This level teaches `by_cases` on membership, which is a useful proof strategy but not what the plan specified. The result is that V4 (finset induction) has one fewer supported practice level than planned. The `by_cases` lesson is pedagogically sound but doesn't reinforce the world's central theme of finset induction.

2. **L06 (SubsetCardInequality) — too easy?**: This is a one-liner (`exact Finset.card_le_card h`). The learner applies a single lemma. The introduction and conclusion are informative, but the proof exercise is trivially short. Consider either:
   - Adding a second part (e.g., prove the subset first, then apply card_le_card)
   - Making the statement require a subset proof step before the cardinality step

### 5b. World-level issues

The world has 9 levels with a clear arc. The center of gravity is finset induction, which is coherent. No splitting needed.

---

## 6. Learner Simulation

### Attentive novice

**First likely stuck point**: L02 insert case — after `right`, the novice may not know `Finset.insert_nonempty`. The hint rescues well (visible hint says the set is nonempty, hidden hint gives the exact lemma).

**Most likely wrong move**: In L03, the novice may try `omega` in the base case instead of `rfl`. This would succeed (omega can close `0 = 0`), which is fine — both are valid.

**Most likely confusion**: L04's vacuous truth pattern. The novice may not understand why `absurd` is the right move. The hint explains "the empty finset is not nonempty" but does not explain what `absurd` does as a tactic. If `absurd` has never been taught (and it hasn't been via `NewTactic`), the novice has no reference for its syntax. **This is a hidden prerequisite leak (F1).**

**Hint rescue quality**: Generally good. L07 has the most complex proof (5+ steps in the inductive case) and the hidden hint shows the full code block, which is helpful. However, the `have hmem` intermediate step in L07 is a multi-line construction that the novice must type correctly before getting feedback — mild P2 concern.

### Experienced Lean user

**Avoidable friction**: L06 is a one-liner that an experienced user can solve instantly but must still read through a lengthy introduction. This is fine for a lecture world — the introduction teaches the concept.

**Alias gaps**: `Finset.card_eq_zero` is disabled in L03 but an experienced user might try `rw [Finset.card_eq_zero] at h`. The DisabledTheorem correctly blocks this. No alias gap.

**`simp` frustration**: An experienced user will immediately try `simp` on L01 and it will succeed (since `simp` is not disabled). This teaches nothing about induction. **P0 exploit.**

**Inventory clutter**: `Finset.insert_union` appears in L05's inventory when it's not used until L09. The experienced user sees it in their theorem panel 4 levels before it's relevant.

---

## 7. Boss Integrity (L09)

### Seeded subskills

| Subskill | Where seeded | Status |
|----------|-------------|--------|
| `Finset.induction_on` syntax | L02 | Seeded and practiced (L02, L03, L04) |
| `card_insert_of_notMem` with `ha` | L03, L04 | Seeded and practiced |
| `Finset.card_insert_le` | L05 (CardInsertLe) | Proved by learner, unlocked in L09 |
| `Finset.insert_union` | Introduced in L05 (wrong level) | Available but not practiced before boss |
| `Finset.empty_union` | L09 (NewTheorem) | First appearance — **not seeded** |
| `have` for intermediate facts | NNG4 baseline | Available |
| `omega` for arithmetic | NNG4 baseline | Available |

### Issues

1. **`Finset.empty_union` is introduced in the boss (L09) via NewTheorem without prior practice.** The learner sees this theorem for the first time in the boss. It's straightforward (hint tells them to use it), but it adds a small surprise burden. P2.

2. **`Finset.insert_union` has no practice level.** It's declared in L05 but never used until L09. The learner must discover it from the boss hints. P2.

3. **Integration quality**: The boss genuinely integrates finset induction (L02-L04), `card_insert_of_notMem` (L03), `card_insert_le` (L05), and `have` for intermediate results. The learner must plan a multi-step proof with intermediate `have` statements and arithmetic combination via `omega`. This is real integration, not concatenation. **Passes the gauntlet test.**

4. **Closure quality**: The boss proof follows the skeleton provided in the introduction. The skeleton is quite detailed — it essentially gives the proof plan. This reduces the planning challenge. The boss is more of a "follow the recipe" than a "plan the proof" exercise. This is acceptable for a lecture world boss but could be more challenging.

---

## 8. Technical Risks

### 8a. Build warnings (from this world)

1. Missing `TacticDoc` for `native_decide`, `aesop`, `simp_all` (L09:153) — these exist in MultisetHierarchy but the build still warns. Likely a build-order issue; low severity.

2. Missing `TheoremDoc` for `Finset.card_union_le` (L09:154) — the theorem is in `DisabledTheorem` but has no doc. **Must add.**

3. "No world introducing `induction`" — needs `NewTactic induction` + `TacticDoc`.

4. "No world introducing `Finset.mem_range`" — used in L07 but never declared. Needs `NewTheorem` + `TheoremDoc` in L07 or a prerequisite.

5. "No world introducing `absurd`" — used in L04. Needs `NewTactic` or equivalent.

6. "No world introducing `case`" — used throughout. Needs `NewTactic`.

7. "No world introducing `Insert.insert`" — used throughout. This is a Lean 4 type class method; may not need explicit declaration but the build warns.

### 8b. Orphan file

`L05_CardinalityByInduction.lean` is present on disk but not imported. It declares `Level 5` (conflicting with `L05_CardInsertLe.lean`). **Delete or rename.** Having two files with the same Level number is a maintenance hazard.

### 8c. `NewTheorem` misplacement

`Finset.insert_union` has `NewTheorem` and `TheoremDoc` in L05_CardInsertLe where it is not used. It should be in L09 (or a coaching level before L09). Similarly, `Finset.card_insert_le`'s `TheoremDoc` is in L05 (correct — it's proved there) and its `NewTheorem` is in L09 (correct — it's re-enabled there). But `insert_union` has both in L05, which is wrong.

---

## 9. Ranked Patch List

### P0 (blocking — must fix)

1. **Add `simp` to DisabledTactic in L01, L02, L03, L04, L05_CardInsertLe, L06, L08, L09.** Standard disabled set: `trivial decide native_decide simp simp_all aesop`. This is the systemic `simp` exploit. L07 already has it.

2. **Add `norm_num` to DisabledTactic in L06.** `norm_num` closes the concrete cardinality comparison without using `card_le_card`.

3. **Delete orphan `L05_CardinalityByInduction.lean`** or integrate it properly. Having two Level 5 files is a build and maintenance hazard.

### P1 (high — should fix)

4. **Add `TheoremDoc` for `Finset.card_union_le`** in L09. Build warns about missing doc for disabled theorem.

5. **Move `NewTheorem Finset.insert_union` from L05_CardInsertLe to L09.** Also move the `TheoremDoc` for `insert_union` to L09. The theorem is not used until L09.

6. **Add `NewTactic induction` + `TacticDoc induction`** in L01 (or L02). The central tactic of the world should be formally declared.

7. **Add `NewTheorem Finset.mem_range` + `TheoremDoc`** in L07 (where it's used).

8. **Add `NewTactic absurd` + `TacticDoc absurd`** in L04 (first use) or in a prerequisite world.

9. **Add `NewTactic case` + `TacticDoc case`** in L02 (first use of `case empty => ... case insert => ...`).

### P2 (medium — consider fixing)

10. **L06 enrichment**: The level is a one-step proof (`exact Finset.card_le_card h`). Consider adding a prerequisite step (e.g., "first prove `{1, 2} ⊆ {1, 2, 3}`, then apply `card_le_card`") to make the level more engaging.

11. **Seed `Finset.empty_union` before the boss.** It appears in L09's `NewTheorem` but is never practiced before. Add a coaching level or practice step before L09.

12. **Seed `Finset.insert_union` with a practice level.** It's introduced but never exercised until the boss. Add a coaching level or include it in an earlier proof.

13. **L09 boss skeleton detail**: The introduction gives a nearly complete proof skeleton. Consider reducing the skeleton to a strategy outline to increase the planning challenge.

14. **L07 multi-line `have` block**: The `have hmem` construction requires 3 lines before feedback. Consider breaking it into hint-supported steps.

### P3 (low — cosmetic)

15. **L05_CardInsertLe plan drift**: The plan says L05 should be "A cardinality-by-induction proof" but it's "Cardinality and insertion" via `by_cases`. Update the plan or restructure the level. (The `by_cases` lesson is pedagogically sound, so updating the plan is reasonable.)

16. **`NewTheorem` in L05_CardInsertLe**: Currently declares `Finset.insert_union` — should be removed after moving to L09. If L05 needs a `NewTheorem`, it could formally re-introduce `Finset.card_insert_le` as the proved result (but it's disabled in that level).

---

## 10. What to Playtest Again After Patching

1. **After P0 fixes (simp/norm_num disabling)**: Re-check every level for remaining exploit paths. Specifically test:
   - `simp` with various argument combinations (since DisabledTheorem should block explicit use but default simp lemmas might still fire)
   - `norm_num` on any level with concrete numerical values
   - `omega` on arithmetic goals (already disabled in L01; check others)

2. **After P1 fixes (inventory)**: Verify build compiles cleanly with no "No world introducing" warnings for the fixed items.

3. **After orphan deletion**: Verify Level 5 numbering is clean and the world file imports correctly.

4. **After boss seeding fixes**: If `empty_union` or `insert_union` practice levels are added, re-audit the boss for integration quality and the world for level count coherence.
