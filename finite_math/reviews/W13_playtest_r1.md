# W13 FinsetSum -- Playtest Audit Round 1

**Auditor**: lean4game-playtest-auditor
**World**: W13 FinsetSum (9 levels, L01-L09)
**Type**: LECTURE
**Round**: R1
**Date**: 2025-03-15

---

## 1. Overall Verdict

**FAIL** -- 3 P0 defects, 3 P1 defects, 3 P2 defects.

The world builds successfully but has critical exploitability problems across multiple levels. Most concrete-statement levels (L01, L02, L07, L08, L09) are closable by `decide`, `native_decide`, or `rfl`, and L07's solution uses `norm_num` while simultaneously disabling it for the player. The boss (L09) is closable by `rfl` in one step -- no decomposition, no `sum_union`, no `sum_insert`, no `sum_singleton`. The world's entire pedagogical promise is defeated.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | `sum_empty`, `sum_cons` introduced but never retrieved. Boss skips both. |
| 2. Granularity fit | 3 | Each level has one dominant lesson. L04/L05 are near-identical but serve a structural contrast. |
| 3. Proof-move teaching | 2 | Intended proof moves (peel off elements, supply membership proofs) are taught in text but bypassed by exploits. |
| 4. Inventory design | 3 | Theorems unlocked at right time. No NewTactic needed (all tactics pre-taught). |
| 5. Hint design / recoverability | 2 | L07 hints tell the learner to use `norm_num` which is disabled. L09 hints are well-layered but irrelevant when `rfl` closes the goal. |
| 6. Worked example -> practice -> boss | 2 | Boss is bypassable by `rfl`. Intended integration is sound in principle but not enforced. |
| 7. Mathematical authenticity | 3 | Intros/conclusions are mathematically honest. L06 AddCommMonoid motivation is well done. All Nat, no Int/Rat. |
| 8. Paper-proof transfer | 3 | L09 conclusion has a good transfer paragraph. L06 conclusion connects to List.sum vs Finset.sum. |
| 9. Technical fit | 2 | L07 DisabledTactic contradiction is a build-logic error. Missing `norm_num` availability for player. |

**Average**: 2.4 -- below the 3.0 threshold. Two categories below 2.

---

## 3. Coverage Gaps

### Items with weak closure

| Item | Axis | State | Notes |
|------|------|-------|-------|
| `Finset.sum_empty` | MATH | I only | Introduced in L02, never retrieved or integrated. Not in boss. |
| `Finset.sum_cons` | MATH | I only | Introduced in L04, never retrieved or integrated. Boss uses `sum_insert` only. |
| `Finset.sum_singleton` | MATH | I, S, G | L01 (I), L03 (S), L07 (S), L09 (G). Healthy closure. |
| `Finset.sum_insert` | MATH | I, S, G | L05 (I), L07 (S), L09 (G). Healthy closure. |
| `Finset.sum_union` | MATH | I, G | L08 (I), L09 (G). Missing supported practice. |
| "Supply membership proof via `have`" | MOVE | I, S | L07 (I), L08 (S), L09 (G). Healthy closure if boss actually forces it. |
| "Decompose concrete sum step-by-step" | MOVE | I only | L07 introduces the pattern but it is bypassable in L07 and L09. |
| AddCommMonoid requirement | MATH | W only | L06 is a conceptual warning. Adequate. |

**Critical gap**: `sum_empty` and `sum_cons` are dead weight in this world. Neither appears after introduction. The plan says `sum_empty` will be retrieved in W14 (induction base case), which is acceptable for cross-world closure but means the within-world coverage is weak.

---

## 4. Granularity Defects

### L04 and L05 near-identical structure
Both levels are "apply `exact Finset.sum_xxx ha`." The learner does the exact same thing twice with a different lemma name. The L05 conclusion contrasts the two, but the levels themselves don't create any experiential difference. **P2 (medium)** -- the text scaffolding partially rescues this.

### L01 and L03 overlap
L01 proves `sum x in {2}, x = 2` using `sum_singleton`. L03 proves `sum x in {a}, f x = f a` using `sum_singleton`. L03 adds generality (free variables) but the proof is still `exact Finset.sum_singleton f a`. The step from concrete to abstract is valid but both levels are one-liners. **P2 (medium)** -- acceptable as gentle practice.

### Boss (L09) too easy even for the intended path
The intended boss proof is: `have` disjointness, `rw sum_union`, `have` non-membership, `rw sum_insert`, `rw sum_singleton`, `rw sum_singleton`. That is 6 tactic steps, but the integration is purely mechanical -- the learner replays L07 and L08 in sequence with no novel interaction between the parts. This is a **gauntlet boss**: it concatenates L07 (concrete computation) and L08 (union splitting) without any new planning challenge. The `have` steps for membership proofs are the only thread connecting the parts, and those are taught in L07.

---

## 5. Learner Simulation

### Attentive Novice

**First likely stuck point**: L07 -- the learner must construct `have` proofs for non-membership inline. The hints guide this well, but the pattern (`have h : ... := by norm_num; rw [...]`) is new cognitive load in a "computing a concrete sum" level. If `norm_num` is disabled (current state), the learner literally cannot follow the hints.

**Most likely wrong move**: In L07, trying `norm_num` (as the hint suggests) and being told it is disabled. The learner has no fallback -- `decide` and `native_decide` are also disabled. The only option would be something like `omega` for the final arithmetic, but the membership proofs (`1 not in {2,3}`) cannot be closed by `omega`.

**Hint rescue quality**: Hints in L01-L06 are adequate. L07 hints are broken (reference a disabled tactic). L08-L09 hints work but are irrelevant when `rfl`/`decide` close the goal.

**Lesson legibility**: The lesson ("decompose a Finset.sum step by step using API lemmas") is clear from the text but not enforced by the type system. A learner who discovers `rfl` or `decide` learns nothing about sum decomposition.

### Experienced Lean User

**Avoidable friction**: None -- the one-liner levels (L01-L05) are quick for an experienced user.

**Exploit paths**: An experienced user will immediately try `decide` or `rfl` on concrete statements. L01, L02, L07, L08, and L09 all fall to these tactics. The entire world can be completed in under 30 seconds with no engagement.

**Alias gaps**: None identified.

**Inventory clutter**: No issues -- theorems are introduced at a clean pace.

---

## 6. Boss Integrity Notes (L09)

### Seeded subskills
- `sum_union` -- seeded in L08. OK.
- `sum_insert` -- seeded in L05, practiced in L07. OK.
- `sum_singleton` -- seeded in L01, practiced in L03 and L07. OK.
- `have` for disjointness -- seeded in L08. OK.
- `have` for non-membership -- seeded in L07. OK.
- `norm_num` in `have` -- used in earlier worlds. OK (if not disabled).

### Closure quality
All boss subskills have been introduced and practiced. No hidden prerequisite leaks. **Adequate** in principle.

### Integration quality
**FAIL** -- The boss is a gauntlet. It concatenates `sum_union` (from L08) then `sum_insert` + `sum_singleton` (from L07) in sequence. There is no novel interaction between `sum_union` and `sum_insert`. The learner never needs to see the whole structure. The proof is strictly sequential: split, peel, singleton, singleton. Any level that uses `sum_union` will naturally require `sum_insert` and `sum_singleton` afterward, so the "integration" is trivially forced by the API, not by a planning challenge.

### Surprise burden
None -- the boss is, if anything, too easy. The only difference from L08 + L07 is that it's in one proof.

### Explainability
A learner could explain: "I split the sum over the union, then decomposed each part into individual terms." This is a valid explanation, so the boss is mathematically coherent. But it is not a genuine integration challenge.

---

## 7. Technical Risks

### T1. L07 DisabledTactic contradiction (P0 -- blocking)
L07 disables `norm_num` (line 82) but the solution uses `norm_num` on lines 46, 53, and 59. The model proof compiles because `DisabledTactic` only applies to the player's interactive session, but **the player cannot replicate the intended proof**. The hints tell the player to use `norm_num`, which is disabled. This is a direct contradiction.

**Fix**: Remove `norm_num` from L07's DisabledTactic line. `norm_num` alone cannot close the full L07 goal (it can close the arithmetic subgoals after the sum decomposition, but it cannot handle `Finset.sum` normalization by itself). Wait -- actually, testing shows `norm_num` closes the entire L07 goal in one shot. So if `norm_num` is enabled, the learner bypasses the entire decomposition. This is the dilemma the enrichment R1 identified.

**Real fix**: The statement must be restructured so that `norm_num` cannot close it. Options:
1. Use variables instead of concrete numbers: `(s : Finset Nat) (hs : s = {1, 2, 3})` then prove `∑ x in s, x^2 = 14`. This forces the learner to `rw [hs]` first, then decompose.
2. Use a non-numeric function that `norm_num` cannot evaluate.
3. Accept `norm_num` as a valid alternative and don't disable it, but add a "try doing it without `norm_num`" hint.

### T2. Multiple levels closable by `rfl` (P0 -- blocking)
The following levels are closable by `rfl`:
- **L01**: `∑ x ∈ ({2} : Finset Nat), x = 2` -- `rfl` closes it.
- **L02**: `∑ x ∈ (∅ : Finset Nat), (x ^ 2) = 0` -- `rfl` closes it.
- **L03**: `∑ x ∈ ({a} : Finset Nat), f x = f a` -- `rfl` closes it.
- **L08**: concrete union equation -- `rfl` closes it.
- **L09** (boss): `∑ x ∈ ({1, 2} : Finset Nat) ∪ {3}, (2 * x) = 12` -- `rfl` closes it.

`rfl` cannot be disabled. This means the intended proof moves (using `sum_singleton`, `sum_empty`, `sum_union`, etc.) are completely optional. The learner learns nothing.

**Fix options for each level**:
- L01, L02, L03: Since these are introduction levels, `rfl` closing them is a P2 annoyance, not a P0. The learner is guided by hints to use the API lemma. The lesson is legible even if `rfl` works. Downgrade to **P2**.
- L08, L09: These are the critical levels. `rfl` closing the boss destroys the world's pedagogical contract. These need statement redesign. Options:
  - Use abstract finsets with hypotheses instead of concrete literals.
  - Use a function that `rfl` cannot evaluate (e.g., a function with a conditional).

### T3. Multiple levels closable by `decide` (P0 -- blocking)
The following levels are closable by `decide` (which IS disabled):
- L01, L02, L07, L08, L09.

`decide` IS in DisabledTactic for all levels, so this is **correctly blocked**. No action needed.

### T4. Multiple levels closable by `norm_num` (P1)
- L01, L07, L08, L09 are all closable by `norm_num`.
- `norm_num` is NOT in DisabledTactic for L01, L02, L08, L09.
- `norm_num` IS in DisabledTactic for L07 (but is used in the solution -- see T1).

For L08 and L09, `norm_num` as a one-shot bypass means the learner never uses `sum_union`, `sum_insert`, or `sum_singleton`. This is a P1 issue because `norm_num` has been taught in W2 and is available.

**Fix**: Add `norm_num` to DisabledTactic on L08 and L09. But then L08's solution needs non-membership proofs via `omega` or `Finset.not_mem_singleton` etc. instead of `norm_num`. This cascade needs careful handling.

### T5. `ring` closes L06 (P2)
L06 is closable by `ring`. `ring` is not in DisabledTactic. However, the intended lesson is about commutativity of addition, and `ring` is a reasonable tactic for that. The lesson is about the concept (why AddCommMonoid is needed), not the tactic. **P2 -- acceptable.**

---

## 8. Ranked Patch List

### P0 (Blocking -- must fix before world passes)

1. **L09 Boss closable by `rfl`**: The boss can be completed by typing `rfl`. No decomposition, no union splitting, no membership proofs. The entire world's integration promise is void. Fix: redesign the boss statement to use abstract finsets with hypotheses, so `rfl` cannot close it. For example:
   ```
   Statement (s t : Finset Nat) (hs : s = {1, 2}) (ht : t = {3})
       (hd : Disjoint s t) :
       ∑ x ∈ s ∪ t, (2 * x) = 12
   ```
   This forces `rw [hs, ht]` or `subst`-style steps first, then the decomposition.

2. **L07 DisabledTactic contradiction**: The solution uses `norm_num` but `norm_num` is disabled for the player. The hints tell the player to use `norm_num`, which is forbidden. Fix: Either (a) remove `norm_num` from DisabledTactic and accept that it's a valid alternative, or (b) redesign L07 to not use `norm_num` in the solution (use `omega` for arithmetic, `Finset.not_mem_singleton.mpr` or similar for membership proofs). Option (b) is better because `norm_num` closes the entire goal.

3. **L08 closable by `rfl` and `norm_num`**: The sum-union level can be bypassed entirely. Fix: use abstract finsets with hypotheses (same pattern as boss fix), or add `norm_num` to DisabledTactic and verify `rfl` is blocked when abstract.

### P1 (High -- should fix)

4. **L01, L02, L03 closable by `rfl`**: The introduction levels are closable by `rfl`. Since these are first-contact levels with heavy hint guidance, this is a reduced risk -- the learner is more likely to follow hints. But an experienced user skips the lessons entirely. Fix: accept as P2 for L01/L02/L03 since they are introductory (the text and hints drive the lesson). Alternatively, abstract the statements.

5. **`sum_empty` has no retrieval**: Taught in L02, never used again. The plan says it will be retrieved in W14 (induction base case). Acceptable for cross-world closure, but the world currently teaches a lemma that is immediately forgotten. Fix: consider adding a retrieval level that involves `sum_empty` (e.g., a level where the learner simplifies `∑ x ∈ ∅ ∪ s, f x = ∑ x ∈ s, f x` using `sum_union` + `sum_empty`).

6. **`sum_cons` has no retrieval**: Taught in L04, never used again. The boss uses `sum_insert` exclusively. Fix: either (a) use `sum_cons` in the boss alongside `sum_insert`, or (b) explicitly mark L04 as preparatory for W14 (where cons may appear in induction proofs). The plan assigns both to M24 (S), but the boss tests only `sum_insert`.

### P2 (Medium -- consider fixing)

7. **Boss is a gauntlet**: L09 concatenates L07's decomposition pattern and L08's union-splitting without novel integration. The "planning challenge" is zero -- the learner knows to split first, then decompose. Fix: make the boss require an unexpected interaction, e.g., a sum where the learner must reorder terms (using AddCommMonoid commutativity from L06) before `sum_union` applies, or where `sum_cons` is needed alongside `sum_insert`.

8. **L04/L05 structural near-duplication**: Both are "exact Finset.sum_xxx ha." The contrast is in the prose only. Fix: modify L05 to require something different (e.g., show that `insert a s` where `a in s` doesn't change the sum, contrasting with `cons` which requires `a not in s`).

9. **`ring` closes L06**: The intended omega-based proof could be replaced by `ring`. Not harmful since the lesson is conceptual, but if `ring` is untaught at this point, it is an alias gap. Fix: no change needed; `ring` is a reasonable alternative.

---

## 9. What to Playtest Again After Patching

After fixing P0 items 1-3:

1. **L07**: Verify the player can complete the intended proof with whatever tactic replaces `norm_num` in the solution. Verify `norm_num` alone does not close the goal (if redesigned).

2. **L08**: Verify the player can supply disjointness proofs. If `norm_num` is disabled, verify an alternative (e.g., `omega` + `Finset.disjoint_left`, or `exact?`) exists and is hinted.

3. **L09 Boss**: Verify `rfl` does not close the redesigned statement. Verify all subskills are still seeded. Verify hints match the new proof structure.

4. **Full exploit sweep**: Re-test all 9 levels with `rfl`, `decide`, `native_decide`, `norm_num`, `omega`, `ring`, `trivial`, `simp`, `aesop` after patches.

5. **Check `sum_empty` retrieval**: If a retrieval level was added, verify it has hints and is properly placed in the level ladder.

---

## Appendix: Exploit Test Results

| Level | rfl | decide | native_decide | norm_num | omega | ring | trivial | simp | Notes |
|-------|-----|--------|---------------|----------|-------|------|---------|------|-------|
| L01 | PASS | PASS | -- | PASS | FAIL | -- | disabled | disabled | rfl/decide/norm_num all close it |
| L02 | PASS | PASS | -- | -- | -- | -- | disabled | disabled | rfl/decide close it |
| L03 | PASS | FAIL | -- | -- | -- | -- | disabled | disabled | rfl closes it; decide fails (free vars) |
| L04 | FAIL | -- | -- | -- | FAIL | -- | disabled | disabled | Abstract statement; not exploitable |
| L05 | FAIL | -- | -- | -- | FAIL | -- | disabled | disabled | Abstract statement; not exploitable |
| L06 | FAIL | -- | -- | -- | PASS | PASS | disabled | disabled | omega is intended; ring is alternative |
| L07 | -- | disabled | disabled | disabled* | -- | -- | disabled | disabled | *norm_num disabled but used in solution |
| L08 | PASS | disabled | -- | PASS | -- | -- | disabled | disabled | rfl and norm_num both close it |
| L09 | PASS | disabled | disabled | PASS | -- | -- | disabled | disabled | rfl and norm_num both close boss |

PASS = tactic closes the goal (exploit exists)
FAIL = tactic does not close the goal (safe)
disabled = tactic is in DisabledTactic (blocked for player)
-- = not tested / not relevant
