# W12_ex CountingFunctions -- Playtest Audit R1

**World**: CountingFunctions (W12_ex)
**Role**: Example world (5 levels)
**Predecessor**: CountingPigeonhole (W12, 10 levels)
**Auditor verdict**: BLOCKED -- P0 exploit on 4 of 5 levels

---

## 1. Overall verdict

The world compiles and is well-written pedagogically, but **bare `norm_num` closes L01, L02, L04, and L05 in one shot**, bypassing every `rw` step the levels are designed to teach. `norm_num` is not in the `DisabledTactic` list. This is a P0 blocking defect: the learner can pass 4 of 5 levels without engaging with any of the taught lemmas (`Fintype.card_fun`, `Fintype.card_fin`, `Fintype.card_embedding_eq`, `Fintype.card_bool`).

Additionally, the boss (L05) is structurally a near-clone of L01 -- the proof is `rw [Fintype.card_fun]; rw [Fintype.card_fin, Fintype.card_fin]; norm_num`, which is the same 3-step pattern used in L01 and L04. It does not integrate the injection or surjection material from L02-L03. This makes it a "fake boss" (failure taxonomy #8).

---

## 2. Rubric scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | Counting items covered, but injection/surjection are used in isolation with no integration |
| 2. Granularity fit | 2 | L01 and L04 are nearly identical proof shapes; boss is a clone of L01 |
| 3. Proof-move teaching | 2 | The `rw + rw + norm_num` pattern is repeated 4 times with no variation |
| 4. Inventory design | 3 | L02 introduces `Fintype.card_embedding_eq` and `Nat.descFactorial` with docs; L03 introduces `Fintype.card_le_of_surjective` with docs. No new items in L01/L04/L05 (appropriate) |
| 5. Hint design and recoverability | 3 | Hints are layered (strategy visible, code hidden). But `norm_num` bypass makes them moot |
| 6. Worked example -> practice -> boss | 1 | Boss does not integrate -- it is a surface variant of L01 |
| 7. Mathematical authenticity | 3 | Good concrete enumeration of functions, nice tables in conclusions |
| 8. Paper-proof transfer | 3 | Conclusions consistently translate to plain language. Transfer moment in L05 conclusion is good |
| 9. Technical fit | 2 | Missing TacticDoc for all 6 disabled tactics; `norm_num` exploit |

**Average**: 2.3 -- does not pass (needs >= 3.0 with no category below 2)

---

## 3. Coverage gaps

### 3a. What is covered

| Item | Axis | L01 | L02 | L03 | L04 | L05 |
|------|------|-----|-----|-----|-----|-----|
| `Fintype.card_fun` | MATH | R | | | R | R |
| `Fintype.card_fin` | MATH | R | R | R | R | R |
| `Fintype.card_embedding_eq` | MATH | | I | | | |
| `Nat.descFactorial` | MATH | | I | | | |
| `Fintype.card_le_of_surjective` | MATH | | | I | | |
| `Fintype.card_bool` | MATH | | | | R | |
| Exponential counting | MOVE | S | | | S | S |
| Contradiction via cardinality | MOVE | | | S | | |
| Rewrite-then-compute | LEAN | S | S | | S | S |
| Multiplication principle | TRANSFER | | | | | T |

### 3b. Gaps

1. **`Fintype.card_embedding_eq` has no retrieval or integration** -- introduced in L02 but never used again. The boss does not touch embeddings.
2. **`Fintype.card_le_of_surjective` has no retrieval or integration** -- introduced in L03 but never used again. The boss does not touch surjectivity.
3. **The boss integrates only L01/L04 material** (rewrite-then-compute on function types). L02 and L03 contribute nothing to the boss. This is a coverage closure failure for an example world that claims to explore function counting from multiple angles.

---

## 4. Granularity defects

### 4a. Overfine: L01 and L04

L01 (`Fintype.card (Fin 2 -> Fin 3) = 9`) and L04 (`Fintype.card (Fin 3 -> Bool) = 8`) have identical proof shapes:
1. `rw [Fintype.card_fun]`
2. `rw [Fintype.card_fin, Fintype.card_X]` (where X is `fin` or `bool`)
3. `norm_num`

The pedagogical payload of L04 is the conceptual connection to subsets / power sets / bit strings. That is valuable and belongs in the world. But the proof task is indistinguishable from L01.

### 4b. Fake boss: L05

The boss proof is:
1. `rw [Fintype.card_fun]`
2. `rw [Fintype.card_fin 2]`
3. `rw [Fintype.card_fin]`
4. `norm_num`

This is the same pattern as L01 with the RHS containing `Fintype.card (Fin 3) * Fintype.card (Fin 3)` instead of `9`. The "integration" is purely that the RHS still contains `Fintype.card` terms, which just means an extra `rw` step. The boss does not require combining injection counting, surjection impossibility, or any reasoning beyond what L01 already taught.

A proper boss for this world should integrate the injection/surjection material from L02-L03 with the counting material from L01/L04.

---

## 5. Learner simulation

### 5a. Attentive novice

**First stuck point**: L01 -- the novice must recall `Fintype.card_fun` from W12. The introduction mentions it, and the hint gives it. This should work.

**Most likely wrong move**: Trying `norm_num` as the first tactic in L01 (it works! -- P0 exploit).

**Hint rescue**: Hints are well-layered -- strategy first, code hidden. But the `norm_num` one-shot means the novice might never see them.

**Lesson legibility**: If the learner uses `norm_num` to close everything, the lesson is "norm_num solves cardinality problems." That is the opposite of what the world intends to teach.

### 5b. Experienced Lean user

**Avoidable friction**: None -- the proofs are short and clean.

**Alias gaps**: `Fintype.card_fin` auto-fills the argument in L05 (`rw [Fintype.card_fin 2]` vs `rw [Fintype.card_fin]`). The hint at line 52-54 of L05 shows `rw [Fintype.card_fin]` without the explicit `2` argument. This might confuse if Lean's unifier doesn't pick the right match. Actually the intended proof has `rw [Fintype.card_fin 2]` (with explicit arg) followed by `rw [Fintype.card_fin]` (without). The hint should clarify which `Fin _` is being resolved.

**Inventory clutter**: Minimal -- only 3 new items across the world. Clean.

**Needless verbosity**: The 3-step `rw; rw; norm_num` pattern is repeated 4 times. An experienced user would just type `norm_num` once.

---

## 6. Course-role sanity

**Intended role**: Example world -- concrete exploration of counting functions.

**Actual role**: L01 and L04 are retrieval exercises on `Fintype.card_fun`. L02 and L03 are first-contact levels for new lemmas (`card_embedding_eq`, `card_le_of_surjective`). L05 is a clone of L01.

**Miscast elements**:
- L02 and L03 introduce new abstract theory (`card_embedding_eq`, `card_le_of_surjective`) in what is supposed to be an example world. An example world should exercise existing theory on concrete ground, not introduce new abstract items. Per the plan, L02's dominant lesson is "counting with constraints" and L03's is "pigeonhole in reverse" -- both are new mathematical ideas, not examples of existing ideas.
- L05 boss is miscast -- it behaves like a worked example, not a boss.

---

## 7. Boss integrity check

| Check | Verdict |
|-------|---------|
| Seeded subskills | FAIL -- L02/L03 skills not required |
| Closure quality | FAIL -- `card_embedding_eq` and `card_le_of_surjective` are introduced but never integrated |
| Integration quality | FAIL -- boss only integrates the `rw + card_fun + card_fin + norm_num` pattern from L01 |
| Surprise burden | PASS -- no new moves required |
| Learner can explain why proof works | PASS (trivially -- it's just "rewrite and compute") |

**Verdict**: Fake boss (failure taxonomy #8). The boss is a surface variant of L01 with no novel integration demand.

---

## 8. Technical risks

### 8a. P0: `norm_num` one-shot exploit on L01, L02, L04, L05

**Verified**: bare `norm_num` (no arguments) closes L01, L02, L04, L05 in a single tactic.

**Impact**: 4 of 5 levels can be bypassed entirely. The learner never engages with `Fintype.card_fun`, `Fintype.card_fin`, `Fintype.card_embedding_eq`, or `Fintype.card_bool`.

**Fix**: Add `norm_num` to `DisabledTactic` on L01, L02, L04, L05. The intended proofs use `norm_num` as the final arithmetic step -- replace with `omega` or redesign the final step. Alternatively, keep `norm_num` available but restructure statements so `norm_num` alone cannot close them (hard to do for cardinality equalities).

**Recommended fix**: Disable `norm_num` on all 5 levels. For the final arithmetic step (`3 ^ 2 = 9`, etc.), use `Hint` to suggest `rfl` or manual computation. Test whether `rfl` closes the final numeric goals after rewrites.

### 8b. P1: Missing TacticDoc for 6 disabled tactics

Build emits `Missing Tactic Documentation` info messages for `trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all` on every level. Add `TacticDoc` entries in L01 (first level of world).

### 8c. P2: Boss does not integrate L02/L03 material

See granularity defects above. The boss is a clone of L01.

### 8d. P2: Example world introduces new abstract theory

L02 introduces `Fintype.card_embedding_eq` and `Nat.descFactorial`. L03 introduces `Fintype.card_le_of_surjective`. These are new abstract lemmas, not examples of previously taught material. An example world should exercise what was already taught, on concrete objects.

---

## 9. Ranked patch list

| Priority | Level(s) | Issue | Fix |
|----------|----------|-------|-----|
| **P0** | L01, L02, L04, L05 | `norm_num` one-shot exploit | Add `norm_num` to `DisabledTactic` on all 5 levels. Replace `norm_num` in intended proofs with a non-exploitable arithmetic closer (test `rfl`, or use `omega` if it works on the post-rewrite goals) |
| **P1** | L01 | Missing TacticDoc for 6 disabled tactics | Add `TacticDoc` blocks for `trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all` in L01 |
| **P1** | L05 | Fake boss -- does not integrate L02/L03 | Redesign boss to require combining counting, injection counting, and/or surjection impossibility. Example: prove a compound statement like "of the 9 functions Fin 2 -> Fin 3, exactly 6 are injective and 0 are surjective" (requires combining results from L01-L03) |
| **P2** | L02, L03 | Example world introduces new abstract theory | Consider: (a) move `card_embedding_eq` and `card_le_of_surjective` introductions to W12 proper, and have L02/L03 be pure retrieval on concrete instances; or (b) accept that this example world has a "teaching-by-example" role where new lemmas are introduced in concrete settings |
| **P2** | L01, L04 | Overfine -- identical proof shapes | Differentiate L04's proof task: e.g., have the learner prove the result using the subset/power-set connection rather than repeating the `card_fun` approach, or add a step that connects `Fintype.card (Fin 3 -> Bool)` to `2^(Fintype.card (Fin 3))` explicitly referencing the subset interpretation |

---

## 10. What to playtest again after patching

1. After disabling `norm_num`: verify all 5 intended proofs still compile with the replacement arithmetic tactic. Verify no other one-shot exploits remain (test `omega`, `ring`, `decide` on every level).
2. After boss redesign: verify the new boss integrates L02/L03 material, is properly seeded, and has layered hints.
3. After TacticDoc additions: verify build warnings are resolved.
4. Re-run full playtest audit (R2) on all 5 levels.
