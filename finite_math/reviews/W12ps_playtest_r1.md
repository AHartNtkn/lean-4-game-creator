# W12_ps CountingPset — Playtest Audit R1

**World**: CountingPset (7 levels)
**Role**: Pset — retrieval of counting and pigeonhole skills under reduced scaffolding
**Dependency**: CountingPigeonhole -> CountingPset

## 1. Overall Verdict

**NEEDS REVISION.** The world compiles and the DisabledTactic standard set is present on all 7 levels. However, there are three blocking or high-severity issues: (1) `norm_num` is not disabled and one-shots two levels, (2) L04 is a trivial `exact h` level that does not exercise the skills it claims, and (3) the boss is a two-move concatenation (L01 + L02 glued together) rather than genuine integration — it does not use V15 (subset cardinality) as the plan requires.

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| Coverage closure | 2 | V8/V9 retrieval in L04 is fake (trivial `exact h`). Boss omits V15. |
| Granularity fit | 2 | L03 and L04 are one-step `exact` levels. L02 and L05 are near-clones. |
| Proof-move teaching | 2 | Pset, so no new teaching expected, but retrieval quality is weak. |
| Inventory design | 3 | No new items (correct for pset). TheoremTab on boss. |
| Hint design / recoverability | 3 | All hints are hidden — appropriate for pset. Hints give full solutions, acceptable at pset level. |
| Worked example -> practice -> transfer -> boss | 2 | Transfer levels are good but boss is weak (gauntlet). |
| Mathematical authenticity | 3 | Word problems are well-chosen. Transfer conclusions are clear. |
| Paper-proof transfer | 3 | L05 and L06 conclusions are solid transfer moments. |
| Technical fit / maintainability | 3 | Compiles cleanly. Standard structure. |

**Average: 2.6 — below the 3.0 threshold. Two categories at 2.**

## 3. Coverage Gaps

| Gap | Severity | Detail |
|-----|----------|--------|
| V9 not exercised | P1 | L04 claims V9 retrieval but the proof is `exact h`. No contradiction-via-cardinality reasoning happens. |
| V15 not in boss | P1 | Plan says boss integrates V15 (G) but the boss proof uses only pigeonhole + product cardinality. No subset reasoning. |
| V8 exercise is trivial | P1 | L04 asks for `exists x, x in s` given `s.Nonempty`, which is definitionally the same. No real witness extraction (no `obtain`). |

## 4. Granularity Defects

| Defect | Severity | Detail |
|--------|----------|--------|
| L02 and L05 are near-clones | P2 | Both are `apply exists_ne_map_eq_of_card_lt; rw [...]; omega` on different numbers. L05 adds a word-problem frame and paper-proof conclusion, which gives it transfer value, but the Lean proof is identical in structure. |
| L03 is a one-step level | P2 | `exact Finset.card_le_card h`. As retrieval this is borderline acceptable, but the learner gets no multi-step exercise. |
| L04 is a zero-step level | P0 | `exact h` or `assumption`. The hypothesis IS the goal by definition. This is not retrieval — it is a type-unfolding test. |

## 5. Statement Exploitability

| Level | Exploit | Severity | Detail |
|-------|---------|----------|--------|
| L01 | `norm_num` one-shots | P1 | `norm_num` closes the entire goal without any `rw`. Learner bypasses `Fintype.card_prod`, `card_fin`, `card_bool`. |
| L01 | `rfl` one-shots | P2 | Definitional equality. Cannot disable `rfl`. Accept as P2. |
| L04 | `assumption` closes | P0 | See granularity defect above — this is a design issue, not just an exploit. |
| L06 | `norm_num` one-shots | P1 | Same as L01. `norm_num` closes without any `rw`. |
| L06 | `rfl` one-shots | P2 | Definitional equality. Cannot disable `rfl`. Accept as P2. |
| L02/L05/L07 | `norm_num` closes cardinality subgoal after `apply` | P2 | After `apply Fintype.exists_ne_map_eq_of_card_lt`, `norm_num` closes the remaining goal without explicit `rw [Fintype.card_fin, ...]`. Learner still must know the right lemma to apply, but skips the cardinality computation steps. |

## 6. Learner Simulation

### Attentive novice

- **L01**: Straightforward if they remember `Fintype.card_prod`. The introduction lists the needed lemmas. Hidden hint gives the full solution. Low risk of getting stuck.
- **L02**: Same pattern as lecture L08 with different numbers. Should recognize the pattern. Hidden hint is sufficient.
- **L03**: One step. If they remember `Finset.card_le_card`, trivial. If not, the hidden hint tells them.
- **L04**: Confusing. The introduction says "extract a concrete element" and mentions `obtain`, but the proof is `exact h`. A novice who tries `obtain <x, hx> := h` gets two goals (prove `x in s` which is... `hx`). The lesson is unclear.
- **L05**: Identical proof to L02 with a word problem. Novice might not notice the transfer value.
- **L06**: Straightforward. `Fintype.card_fun` + `card_fin` + `norm_num`.
- **L07**: If they solved L01 and L02, this is those two combined. Manageable.

**First stuck point**: L04 — the mismatch between the introduction's promise ("extract a concrete element") and the actual proof (`exact h`) is confusing.

**Most likely wrong move**: Trying `obtain` on L04 (which works but creates unnecessary subgoals).

### Experienced Lean user

- **L01/L06**: Will use `norm_num` or `rfl` and skip immediately. No learning value.
- **L02/L05**: Will recognize pigeonhole immediately, use `apply` + `norm_num` (or `omega`).
- **L03**: `exact Finset.card_le_card h` — trivial.
- **L04**: `exact h` or `assumption` — trivial.
- **L07**: `apply` + `norm_num` — trivial.

**Avoidable friction**: None for the experienced user. The world is too easy for them but that is partially expected in a pset.

## 7. Boss Integrity (L07)

### Seeded subskills
- Product cardinality (`Fintype.card_prod`): seeded in L01. OK.
- Pigeonhole (`exists_ne_map_eq_of_card_lt`): seeded in L02, L05. OK.
- Cardinality evaluation (`Fintype.card_fin`): seeded in L01, L02. OK.
- Arithmetic (`omega`): used throughout. OK.
- **Subset reasoning (V15)**: NOT seeded. L03 exercises V15 but the boss does not use it. Plan says it should.

### Closure quality
Partial. The boss is a 3-step proof that combines L01 and L02. It does not integrate L03 (subset cardinality) or L04 (witness extraction).

### Integration quality
**GAUNTLET BOSS.** The boss is `apply pigeonhole; rw [card_prod, card_fin, card_fin]; omega`. This is L02's proof with L01's product cardinality step inserted. There is no novel interaction between the parts — the learner replays L01 inside L02. No planning challenge, no new structural insight.

### Surprise burden
Zero. The boss introduces nothing new. This is appropriate for a pset boss but the integration demand is too weak.

### Can a learner explain why it works?
Yes, trivially: "the product type has 9 elements, the codomain has 8, so by pigeonhole two inputs collide." This is the same explanation as L02 with a cardinality computation prepended. No deeper insight emerges.

**Verdict**: The boss fails the gauntlet-boss test. It should integrate at least three distinct proof moves from the world, including V15 (subset reasoning). Currently it integrates only two (product cardinality + pigeonhole).

## 8. Pset Integrity

### Fresh surface form
- L01: `Fin 4 x Bool` vs lecture's `Fin 2 x Fin 3`. Fresh. PASS.
- L02: `Fin 7 -> Fin 5` vs lecture's `Fin 5 -> Fin 4`. Fresh. PASS.
- L03: Abstract `s subset t` vs lecture's concrete finsets. Fresh. PASS.
- L04: Generic `s.Nonempty` — but the proof is trivial. FAIL (see below).
- L05: `Fin 8 -> Fin 7` (students/groups) vs lecture's `Fin 6 -> Fin 5` (people/rooms). Fresh. PASS.
- L06: `Fin 4 -> Fin 3` vs lecture's `Fin 2 -> Fin 3`. Fresh. PASS.
- L07: `Fin 3 x Fin 3 -> Fin 8`. Fresh compound type. PASS.

### Reduced scaffolding
All hints are hidden. No visible hints. PASS.

### Real retrieval
- L01: Real retrieval of product cardinality. PASS.
- L02: Real retrieval of pigeonhole. PASS.
- L03: One-step `exact`. Minimal retrieval. BORDERLINE.
- L04: `exact h` — no retrieval. FAIL.
- L05: Real retrieval (same as L02). PASS but near-clone.
- L06: Real retrieval of function cardinality. PASS.
- L07: Retrieval of L01 + L02 combined. PASS but shallow.

### Not cloning lecture material
- L02 and L05 are structurally identical to lecture problems (same proof pattern, different numbers). This is acceptable for a pset IF the surface form is genuinely different. The word-problem framing in L05 adds transfer value. BORDERLINE PASS.

## 9. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| `norm_num` not disabled | P1 | One-shots L01 and L06 entirely. Closes cardinality subgoals in L02/L05/L07. Add `norm_num` to DisabledTactic on L01, and consider adding it on other levels where it bypasses the intended `rw` steps. |
| Build warning about TacticDoc simp_all | P3 | The warning "Missing Tactic Documentation" appears for simp_all at L03:47. The TacticDoc exists in MultisetHierarchy but may be processed after CountingPset due to import ordering. Not a functional issue. |

## 10. Ranked Patch List

### P0 — Blocking

1. **Redesign L04**: The current statement (`s.Nonempty -> exists x, x in s`) is definitionally trivial. Replace with a genuine V8/V9 retrieval problem. Options:
   - (a) Give `h : Fintype.card (Fin 3 oplus Bool) = 0` and ask for `False` (V9 retrieval on fresh type). This was originally the L04 content per my first read — it may have been overwritten. If so, restore it.
   - (b) Give `h : 0 < s.card` and ask for `s.Nonempty` — requires `Finset.card_pos` which exercises the card-to-nonemptiness direction (V8).
   - (c) Give a nonempty finset and ask the learner to produce a specific element using `obtain` and then do something with it (e.g., prove it satisfies a predicate).

2. **Redesign L07 boss**: The boss must integrate V15 (subset cardinality) per plan. Options:
   - (a) Add a hypothesis `h : s subset Finset.univ.filter (...)` and require proving `s.card <= ...` as part of deriving a pigeonhole argument.
   - (b) Combine pigeonhole with a subset-cardinality step: e.g., given `f : Fin 5 -> Fin 3` and `s subset Finset.image f Finset.univ`, prove `s.card <= 3` and then use this to derive something further.
   - (c) Multi-step: count a product type, show a subset is bounded, apply pigeonhole on the full type. This requires 4+ distinct moves (product cardinality, subset monotonicity, pigeonhole, arithmetic).

### P1 — High

3. **Disable `norm_num` on L01**: Add `norm_num` to DisabledTactic. `norm_num` one-shots the entire goal. The intended lesson is `rw [Fintype.card_prod, card_fin, card_bool]`.

4. **Disable `norm_num` on L06 (or restructure)**: L06's intended proof USES `norm_num` as the final step (`rw [card_fun, card_fin, card_fin]; norm_num`). But `norm_num` alone also closes the entire goal. Options: (a) disable `norm_num` and replace the final step with `omega` or explicit arithmetic, or (b) accept that `norm_num` is the intended tool and the learner who uses it alone still demonstrates the right skill (since `norm_num` is taught). Option (b) is defensible if the level's lesson is counting, not rewriting.

5. **Consider disabling `norm_num` on L02/L05/L07**: After `apply`, `norm_num` closes the cardinality subgoal without `rw [Fintype.card_fin, ...]`. The learner skips the explicit cardinality evaluation. This is P2 for L02/L05 (the learner still needs to know which lemma to apply) but P1 for the boss (which should be multi-step, not `apply + norm_num`).

### P2 — Medium

6. **Strengthen L03**: Currently one-step (`exact Finset.card_le_card h`). Consider making it multi-step: e.g., give concrete finsets and require proving the subset relation first, then deriving the cardinality bound.

7. **Address L02/L05 near-duplication**: L02 and L05 have identical proof structures. L05 adds transfer value via the word problem and paper proof, which justifies its existence. But the Lean proof is identical. Consider making L05's proof require an additional step (e.g., a `have` to set up the function) to differentiate it.

### P3 — Low

8. **`rfl` on L01/L06**: Cannot disable `rfl`. Accept as P2. The introduction text steers toward `rw`, and `rfl` is not mentioned in hints.

## 11. What to Playtest After Patching

After implementing fixes:
1. Verify L04 redesign actually exercises V8/V9 (not trivially closable).
2. Verify boss integrates V15 and requires 4+ distinct moves.
3. Verify `norm_num` is blocked on L01 (and L06 if chosen).
4. Verify the boss cannot be closed in 2 steps after `apply`.
5. Re-run full `lake build`.
6. Re-check all 7 levels for new exploits introduced by redesign.
