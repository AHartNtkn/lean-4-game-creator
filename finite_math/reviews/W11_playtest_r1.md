# W11 FintypeClass -- Playtest Audit R1

**World**: FintypeClass (8 levels, Lecture)
**World promise**: The learner understands `Fintype` as the type class that equips a type with a universal finset, and can use `Finset.univ` and `Fintype.card`.
**Build**: Passes (8223 jobs). Build warnings for missing TacticDoc in L08 (pre-existing from earlier worlds).

## 1. Overall Verdict

**BLOCKED -- two P0 exploits, two P0 missing inventory items.**

`simp` is available and closes all 8 levels from the initial goal state. `norm_num` (also available) closes all cardinality goals (6 of 8 levels). Neither is disabled. Additionally, `Fintype.card_fin` and `Fintype.card_prod` -- two core lemmas taught in L04 and L06 respectively -- are never declared via `NewTheorem` and have no `TheoremDoc`, so they never appear in the learner's theorem panel. The world's pedagogical contract is thoroughly undermined: a learner can complete the entire world without engaging with any of the intended content.

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 2 | Core items introduced but two key theorems invisible in inventory |
| Granularity fit | 3 | Each level has a clear dominant lesson; L07 is miscast (see below) |
| Proof-move teaching | 2 | All proofs bypassable via `simp`/`norm_num`/`rfl`; no forced engagement |
| Inventory design | 1 | Two core theorems missing from inventory; `simp` available but undiscussed |
| Hint design | 3 | Hints are layered (strategy + hidden code); L06 hints are reasonable |
| Progression | 2 | Boss is a near-clone of L06 (gauntlet, not integration); see section 5 |
| Mathematical authenticity | 3 | Good conceptual framing; transfer moments present; L07 counterexample is conceptual only |
| Paper-proof transfer | 3 | Conclusions connect to counting principles well |
| Technical fit | 2 | Missing NewTheorem/TheoremDoc; exploit surface; build warnings |

**Average**: 2.3 -- below the 3.0 threshold. Two categories below 2.

## 3. Coverage Gaps

### Missing inventory declarations (P0)

| Item | Where taught | Status |
|------|-------------|--------|
| `Fintype.card_fin` | L04 (first use), L06, L08 | **No `NewTheorem`, no `TheoremDoc`** |
| `Fintype.card_prod` | L06 (first use), L08 | **No `NewTheorem`, no `TheoremDoc`** |

These are core lemmas that the boss requires. Without `NewTheorem`, they never appear in the learner's theorem panel. The learner must remember them from the introduction text alone -- this violates inventory design standards.

### Coverage lifecycle gaps

| Item | I | S | R | G | Notes |
|------|---|---|---|---|-------|
| `Fintype` (def) | L01 | L07 | -- | L08 | No retrieval outside L07's indirect use |
| `Finset.univ` (def) | L01 | L02 | L07 | -- | Never integrated in boss |
| `Finset.mem_univ` | L02 | L07 | -- | -- | No retrieval, no integration in boss |
| `Finset.card_univ` | L03 | L07 | -- | -- | No retrieval, no integration in boss |
| `Fintype.card_fin` | L04 | L06 | -- | L08 | No retrieval |
| `Fintype.card_bool` | L05 | -- | -- | L08 | No supported practice before boss |
| `Fintype.card_prod` | L06 | -- | -- | L08 | No supported practice before boss |

The boss integrates `card_prod + card_fin + card_bool` but never requires `Finset.univ`, `Finset.mem_univ`, or `Finset.card_univ`. These three items (L01-L03) have no integration path. The boss only tests L04-L06 material.

## 4. Granularity Defects

### L07 is miscast (P1)

The title is "Nat is NOT a Fintype" but the actual task is proving a conjunction about `Bool`. The level's framing discusses the counterexample (`Nat` has no `Fintype` instance) but the proof task doesn't involve `Nat` at all. The learner proves `(∀ b : Bool, b ∈ Finset.univ) ∧ Finset.univ.card = 2`.

This is a retrieval/review level for L02+L03+L05, not a counterexample level. The counterexample is only discussed in text. The level is miscast: its narrative promise (showing what breaks for infinite types) is not fulfilled by its proof task.

### Boss is near-gauntlet (P1)

L08 asks: `Fintype.card (Fin 2 x Bool) = 4`. The intended proof is:
1. `rw [Fintype.card_prod]` (from L06)
2. `rw [Fintype.card_fin, Fintype.card_bool]` (from L04, L05)

This is structurally identical to L06's proof (`rw [Fintype.card_prod]` then `simp [Fintype.card_fin]`), except with `Bool` instead of `Fin 3`. There is no novel planning challenge. The boss is a surface-form variation of L06, not a genuine integration.

A better boss would require combining more of the world's repertoire (e.g., involving `Finset.univ`, `Finset.mem_univ`, or `Finset.card_univ` alongside cardinality reasoning).

### L01 vs L03 redundancy risk (P2)

L01 proves `(Finset.univ : Finset (Fin 3)).card = 3` (via `rfl`). L03 proves `(Finset.univ : Finset (Fin 5)).card = Fintype.card (Fin 5)` (via `exact Finset.card_univ`). These are closely related -- L01's goal is also an instance of `Finset.card_univ` composed with `Fintype.card_fin`. The progression is fine conceptually but the connection should be made explicit in L03's introduction (it is, partially).

## 5. Exploitability Analysis

### P0: `simp` closes all 8 levels

`simp` is not in `DisabledTactic` for any level. Bare `simp` (no arguments) closes:
- L01: `simp` closes `(Finset.univ : Finset (Fin 3)).card = 3`
- L02: `simp` closes `∀ x : Fin 3, x ∈ Finset.univ`
- L03: `simp` closes `Finset.univ.card = Fintype.card (Fin 5)`
- L04: `simp` closes `Fintype.card (Fin 7) = 7`
- L05: `simp` closes `Fintype.card Bool = 2`
- L06: `simp` closes `Fintype.card (Fin 2 x Fin 3) = 6`
- L07: `simp` closes the full conjunction
- L08: `simp` closes `Fintype.card (Fin 2 x Bool) = 4`

**Fix**: Add `simp` to `DisabledTactic` for all levels except L06, where `simp [Fintype.card_fin]` is used intentionally. For L06, either (a) keep `simp` disabled and change the intended proof to `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`, or (b) accept `simp` for L06 only and add it to DisabledTactic on all other levels and the boss.

**Recommended approach**: Disable `simp` on all levels. For L06, rewrite the proof and hints to use `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. This keeps the world `simp`-free and forces engagement with the individual lemmas.

### P0: `norm_num` closes 6 of 8 levels

`norm_num` (no arguments) closes L01, L03, L04, L05, L06, L08 -- all the cardinality equalities. It is not disabled.

**Fix**: Add `norm_num` to `DisabledTactic` for all levels.

### P2: `rfl` closes 6 of 8 levels

`rfl` closes L01, L03, L04, L05, L06, L08. This is a known systemic issue (`rfl` cannot be disabled). L01 already acknowledges this by making `rfl` the intended proof. L04 acknowledges it in the introduction text but asks the learner to use `Fintype.card_fin` anyway.

**Accepted as P2**: Cannot disable `rfl`. The text-level framing ("try using the lemma explicitly") is the mitigation.

## 6. Interactive Proof Quality

### L06: `simp` as intended proof step (P1)

The intended proof for L06 uses `simp [Fintype.card_fin]` after `rw [Fintype.card_prod]`. This is problematic because:
1. It teaches `simp` as a cleanup tool, which then enables the `simp` exploit on every other level.
2. The learner doesn't practice applying `Fintype.card_fin` explicitly.

**Fix**: Replace with `rw [Fintype.card_fin, Fintype.card_fin]` which requires the learner to understand that `rw` rewrites one occurrence at a time and they need to apply it twice.

### L01: One-step proof (P2 -- acceptable)

L01 is a first-contact level. `rfl` is the intended proof. This is fine for introduction -- the lesson is about `Fintype` and `Finset.univ`, not about the proof.

## 7. Learner Simulation

### Attentive novice

**First stuck point**: L06. After `rw [Fintype.card_prod]`, the goal becomes `Fintype.card (Fin 2) * Fintype.card (Fin 3) = 6`. The novice knows `Fintype.card_fin` from L04 but may not realize they need to apply it twice (if `simp` is disabled). The hint currently says "use `simp [Fintype.card_fin]`" which won't work if `simp` is disabled.

**Most likely wrong move**: Trying `rw [Fintype.card_fin]` once and being confused when the goal becomes `2 * Fintype.card (Fin 3) = 6` instead of being fully resolved.

**Hint rescue**: Current hints rescue well for most levels. L06's hints need updating if `simp` is disabled.

**Lesson legibility**: The conceptual framing is strong. Each level's introduction clearly explains what is being taught. Transfer moments in conclusions are well-written.

### Experienced Lean user

**Avoidable friction**: The experienced user will just type `simp` or `norm_num` or `rfl` on every level. If those are disabled, they would type `exact Fintype.card_fin 7` etc. -- the proofs are short enough that this is not friction.

**Inventory gaps**: `Fintype.card_fin` and `Fintype.card_prod` not appearing in the theorem panel is confusing for any user who relies on the panel to recall available lemmas.

**Expert alias concern**: An experienced user might try `exact?` or `apply?` -- these are not typically available in lean4game, so no issue.

## 8. Boss Integrity (L08)

### Seeded subskills
- `Fintype.card_prod` -- seeded in L06 (one level of practice, no retrieval) -- **weak closure**
- `Fintype.card_fin` -- seeded in L04, used in L06 -- adequate
- `Fintype.card_bool` -- seeded in L05, no supported practice -- **weak closure**

### Integration quality: LOW
The boss proof is `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]` -- a simple chain of rewrites with no planning challenge. Each step is a direct application of a single lemma. The boss is structurally identical to L06 with `Bool` substituted for `Fin 3`.

### Surprise burden: NONE
No untaught moves. The boss is entirely composed of previously seen material.

### Gauntlet check: YES
The boss concatenates L06's proof pattern with L05's lemma. There is no novel interaction between the parts. The learner replays L06 with a minor substitution.

### Recommendation
Redesign the boss to integrate more of the world's repertoire, particularly `Finset.univ`, `Finset.mem_univ`, and/or `Finset.card_univ` alongside cardinality computation. For example:

```
-- Option A: Require proving membership AND cardinality
Statement : (∀ x : Fin 2 × Bool, x ∈ Finset.univ) ∧ Fintype.card (Fin 2 × Bool) = 4

-- Option B: Use Finset.card_univ bridge explicitly
Statement : (Finset.univ : Finset (Fin 2 × Bool)).card = Fintype.card (Fin 2 × Bool)
            ∧ Fintype.card (Fin 2 × Bool) = 4
```

## 9. Course-Role Sanity

| Level | Intended role | Actual role | Verdict |
|-------|--------------|-------------|---------|
| L01 | First-contact | First-contact (rfl proof) | OK |
| L02 | Supported practice | First-contact (`exact` with new theorem) | OK |
| L03 | First-contact | First-contact (bridge concept) | OK |
| L04 | Supported practice | Supported practice of `Fintype.card` | OK |
| L05 | First-contact | First-contact (new type, same pattern) | OK |
| L06 | Supported practice | Multi-step rewrite practice | OK |
| L07 | Counterexample/warning | Retrieval exercise (miscast -- see below) | **MISCAST** |
| L08 | Boss | Near-gauntlet boss | **WEAK** |

**L07 miscast**: The title promises a counterexample about `Nat` not being `Fintype`. The proof task is about `Bool`. The counterexample is text-only. Either rename the level and drop the `Nat` framing, or redesign the task to actually involve the `Nat` non-instance (e.g., a level that discusses the error message and asks the learner to prove something that does NOT require `Fintype Nat`).

## 10. Technical Risks

1. **Build warnings**: Missing `TacticDoc` for `trivial`, `decide`, `native_decide`, `aesop`, `simp_all` at L08:79. These docs exist in earlier worlds (W3_ex, W4) but the build still warns. Likely a pre-existing issue.
2. **No `NewTheorem` for `Fintype.card_fin`**: Taught in L04, used in L06 and L08, but invisible in theorem panel.
3. **No `NewTheorem` for `Fintype.card_prod`**: Taught in L06, used in L08, but invisible in theorem panel.
4. **L06 uses `simp` in intended proof**: If `simp` is added to `DisabledTactic`, L06's proof and hints must be rewritten.

## 11. Ranked Patch List

| # | Severity | Level(s) | Issue | Fix |
|---|----------|----------|-------|-----|
| 1 | **P0** | ALL | `simp` not disabled; closes all 8 levels | Add `simp` to `DisabledTactic` on all levels. Rewrite L06 proof to use `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. |
| 2 | **P0** | L01,L03-L06,L08 | `norm_num` not disabled; closes 6 of 8 levels | Add `norm_num` to `DisabledTactic` on all levels. |
| 3 | **P0** | L04 | `Fintype.card_fin` missing `NewTheorem` + `TheoremDoc` | Add `NewTheorem Fintype.card_fin` and `TheoremDoc Fintype.card_fin as "Fintype.card_fin" in "Fintype"` to L04. |
| 4 | **P0** | L06 | `Fintype.card_prod` missing `NewTheorem` + `TheoremDoc` | Add `NewTheorem Fintype.card_prod` and `TheoremDoc Fintype.card_prod as "Fintype.card_prod" in "Fintype"` to L06. |
| 5 | **P1** | L06 | Intended proof uses `simp` which should be disabled | Change proof to `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. Update hints. |
| 6 | **P1** | L07 | Level miscast: title says "Nat not Fintype" but task is about Bool | Either (a) rename to "Review: Bool as Fintype" and drop `Nat` framing, or (b) split into two levels: one retrieval exercise on Bool, one conceptual level about Nat's non-instance. |
| 7 | **P1** | L08 | Boss is gauntlet (structurally identical to L06 with substitution) | Redesign boss to integrate L01-L03 material (`Finset.univ`, `Finset.mem_univ`, `Finset.card_univ`) alongside cardinality computation. |
| 8 | **P2** | L05 | `Fintype.card_bool` has no supported practice before boss | Either add a practice level between L05 and L08, or accept this as low-risk since L05 is simple. |
| 9 | **P2** | L01,L03-L06,L08 | `rfl` closes 6 of 8 levels | Accepted -- `rfl` cannot be disabled. Text-level mitigation adequate. |

## 12. What to Playtest Again After Patching

After implementing patches 1-7:
1. Verify `simp` and `norm_num` are properly disabled on all 8 levels (test each).
2. Verify L06's new `rw`-based proof compiles and hints match.
3. Verify `Fintype.card_fin` and `Fintype.card_prod` appear in the theorem panel.
4. Verify the redesigned boss requires genuine integration (not a gauntlet).
5. If L07 is split, verify both new levels compile and have proper hints.
6. Re-run full exploit check (`simp`, `norm_num`, `trivial`, `decide`, `omega`, `rfl`) on all levels.
7. Simulate novice path through L06 with new `rw` proof to confirm hint rescue works.
