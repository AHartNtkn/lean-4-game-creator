# Playtest Audit: InjectiveWorld

**Auditor**: Phase 2d playtest
**Date**: 2026-03-24

---

## 1. Overall Verdict: PASS

This is a well-designed lecture world with clear progression, strong boss integration, and careful exploit blocking. The 8-level structure (2 practice + 1 negation + 2 composition + 1 coaching + 1 left-inverse + 1 boss) delivers on every promise in the world introduction. The coaching level (L06) for `rw at` and `← rw` is an excellent addition beyond the original PLAN, properly seeding the boss's hardest moves. No P0 defects found.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 4 | All core items have intro + supported use; retrieval/transfer appropriately deferred to W12 pset |
| Granularity fit | 4 | Each level has one dominant lesson; L06 pushes with two rw variants but on a trivially simple statement |
| Proof-move teaching | 4 | Canonical injectivity shape is drilled, named, and reinforced; apply chain and rw-at patterns made explicit |
| Inventory design | 3 | Clean: 2 definitions at right times, thorough DisabledTheorem/DisabledTactic. Minor: `congrArg` mentioned in L05 conclusion but never formally introduced via NewTheorem |
| Hint design and recoverability | 4 | Every level has layered hints (strategy visible, code hidden); Branches cover alternatives (have vs change, congrArg vs show+rw, rw+exact vs rw chain) |
| Worked example -> practice -> transfer -> boss | 4 | L01 worked example -> L02 practice -> L04-05 new theorems -> L06 coaching -> L07 combines -> L08 integrates. Clear scaffolding fade |
| Mathematical authenticity | 4 | Concrete examples (n+1, 2*n, n/2), counterexample for non-injectivity, asymmetry explained, left-inverse motivation |
| Paper-proof transfer | 4 | Conclusions consistently translate to natural language; L03's comparison table (proving vs disproving) is excellent; L07's chain-of-equalities walkthrough |
| Technical fit and maintainability | 4 | Clean build, sane dependency (SetWorld only), coherent center of gravity, well-organized disabled lists |

**Average**: 3.89
**Minimum**: 3

---

## 3. Summary Statistics

- 8 levels, 2 new definitions (Function.Injective, Function.LeftInverse)
- Boss requires 7 tactic steps integrating 6 distinct skills from L01-L07
- All 3 library shortcuts (Injective.comp, Injective.of_comp, LeftInverse.injective) properly disabled
- `injection` tactic disabled in arithmetic levels (L01, L02, L08)
- Arithmetic cancel theorems disabled in relevant levels

---

## 4. P0 Defects (Blocking)

None.

---

## 5. P1 Defects (High Priority)

None.

---

## 6. P2 Defects (Medium)

**P2-1: Verify `fun_prop` cannot close injectivity goals.**
`fun_prop` is not in any DisabledTactic list. In current Mathlib, `fun_prop` primarily handles `Continuous`, `Measurable`, etc. and likely cannot prove `Function.Injective`, but this should be verified. If `fun_prop` can close L01/L02/L04/L07/L08, add it to DisabledTactic.

**P2-2: `congrArg` mentioned but not formally introduced.**
L05's conclusion and Branch use `congrArg`, and Metadata.lean has a TheoremDoc for it, but no level has `NewTheorem congrArg`. The learner can use it (the game allows tactics/theorems not in inventory) but won't see it in their theorem panel. This is acceptable for an "advanced alternative" but could confuse learners who read the conclusion, try it, and then can't find it in their panel.

**P2-3: L01 introduction may overstate omega's limitation.**
The introduction says "omega cannot read the lambda form directly" and requires `have h : a + 1 = b + 1 := hab`. If `omega` can in fact close the goal directly after `intro a b hab` (without the `have` step), the introduction is misleading. The `have` step teaches equation extraction, which is valuable for the boss, but the claim about omega should be accurate. Verify whether `intro a b hab; omega` works; if so, reframe the `have` step as "good practice for later" rather than "necessary because omega can't handle it."

---

## 7. Coverage Gaps

None within the scope of a lecture world. All items planned for W09 in the coverage map are present:

| Item | Intro | Support | Integration |
|------|-------|---------|-------------|
| Function.Injective definition | L01 | L02-L08 | L08 boss |
| Canonical injectivity proof shape | L01 | L02 | L08 boss |
| Non-injectivity proof | L03 | -- | -- (deferred to W12) |
| Composition preserves injectivity | L04 | -- | L08 boss (variant) |
| Extraction from composition | L05 | -- | -- (deferred to W12) |
| `rw at` hypothesis | L06 | L07, L08 | L08 boss |
| Backward `rw [←]` | L06 | L07, L08 | L08 boss |
| Function.LeftInverse definition | L07 | L08 | L08 boss |
| Left inverse -> injective | L07 | L08 | L08 boss |

Non-injectivity (L03) and extraction (L05) are not tested in the boss. This is by design: the boss integrates the positive construction skills, and retrieval of L03/L05 is planned for the W12 pset.

---

## 8. Granularity Defects

None. Level count (8) is appropriate. Each level has a clear dominant lesson:

- L01: definition + canonical shape (one conceptual burden)
- L02: same shape, different function (zero new burdens)
- L03: non-injectivity proof shape (one new burden)
- L04: composition + apply chain (one new burden)
- L05: extraction + show-rw pattern (one new burden)
- L06: rw at + backward rw (two variants of known tactic, simple statement)
- L07: LeftInverse definition + instantiation (one new burden, rw skills from L06)
- L08: integration only (zero new burdens)

---

## 9. Learner Simulation Notes

### Attentive novice

**First stuck point**: L03 (non-injectivity). The nested `have key : (0 : ℕ) = 1 := by apply h; rfl` requires understanding that `apply h` with `h : Injective f` unifies the goal with `f`'s output type. The hints guide through this, but the learner may need the hidden hint for the full template.

**Most likely wrong move**: In L05, after `apply hgf`, the learner sees `(g ∘ f) a = (g ∘ f) b` and may try `rw [hab]` directly (which won't work because the goal mentions `f a` inside composition, not bare `f a`). The `show` step and hints address this.

**Hint rescue quality**: Excellent. Every stuck point has a visible strategy hint plus a hidden code hint. The Branch alternatives mean both common approaches are covered.

### Experienced Lean user

**Avoidable friction**: L06 may feel like an interruption from the injectivity theme. The introduction frames it well as preparation for L07, but the statement (fixed-point rewriting) is noticeably disconnected from `Function.Injective`. Acceptable for a coaching level.

**One-liner alternatives**: L04 can be closed with `exact hf (hg hab)` (term-mode), L05 with `exact fun a b h => hgf (congrArg g h)`. These require genuine understanding and are acceptable alternative paths.

**Potential friction**: `injection` is disabled in L01/L02 but the learner isn't told why (no Hint explains "injection is disabled"). The DisabledTactic message from the game server should suffice, but a note in the introduction saying "we disable `injection` so you learn the general pattern" would be friendlier.

---

## 10. Boss Integrity Notes

### Seeded subskills
All 6 skills used in the boss are explicitly taught in prior levels:

| Boss step | Source level |
|-----------|-------------|
| `intro a b hab` | L01-02 |
| `have hab' : ... := hab` | L01-02 |
| `have ha := hinv (f a)` | L07 |
| `rw [hab'] at ha` | L06 |
| `apply hf` | L04-05 |
| `rw [← ha, hb]` | L06-07 |

### Closure quality
The boss requires 7 tactic steps, the longest proof in the world. This is appropriate for a boss. No proof in L01-L07 exceeds 4-5 steps, so the scale-up is moderate (not a surprise burden).

### Integration quality
The boss genuinely integrates: the learner must plan a multi-step strategy that combines left-inverse instantiation with equation extraction, hypothesis rewriting, injectivity application, and backward rewriting. This is not a gauntlet (sequential replay of earlier proofs) — the left-inverse and injectivity interact in a novel way.

### PLAN deviation
The PLAN boss was "Direct injectivity proof + extraction from composition" (two parts). The actual boss is "Left inverse + injectivity -> composition injectivity" (one part). The actual boss integrates more skills (6 vs 3) and tests the harder techniques (L06-L07) that the coaching level was specifically added to teach. This deviation is justified and produces a better boss.

---

## 11. Technical Risks

**Low risk**: `fun_prop` exploit possibility (P2-1 above). Likely not an issue for `Function.Injective` but should be confirmed.

**No risk**: Build is clean (no errors). Dependencies are minimal (SetWorld only). No `open scoped` usage. No multi-line `=>` syntax in hints or text.

---

## 12. Ranked Patch List

1. **Verify `fun_prop`** cannot close L01/L02/L04/L07/L08 goals. If it can, add to DisabledTactic. (P2-1)
2. **Verify `omega` after bare `intro a b hab`** in L01. If it works without `have`, reframe the introduction to present `have` as good practice rather than necessity. (P2-3)
3. **Optional**: Add `NewTheorem congrArg` in L05 if you want it in the learner's theorem panel; otherwise remove the Branch that uses it and keep it as a conclusion-only mention. (P2-2)

---

## 13. What to Playtest Again After Patching

- If `fun_prop` is confirmed exploitable: re-check L01, L02, L04, L07, L08 after disabling
- If L01 `omega` claim is wrong: re-read L01 introduction after reframing
- No structural re-audit needed — the world's design is sound
