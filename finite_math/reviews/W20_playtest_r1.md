# W20 ThreeFiniteness — Playtest Audit R1

**World**: ThreeFiniteness (W20)
**Levels**: 6 (L01–L06)
**Role**: Lecture
**Dependency**: FintypeClass -> ThreeFiniteness
**World promise**: The learner understands the distinctions between `Set.Finite`, `Fintype`, and `Finset`, and can convert between them.

---

## 1. Overall Verdict

**CONDITIONAL PASS — two blocking defects and several substantive issues.**

The world is well-structured conceptually. The three-notion comparison is clear, the progression from introduction through conversion to integration makes pedagogical sense, and the prose quality is high. However, the boss (L06) has two hidden prerequisite leaks (`Set.mem_univ` undeclared, `Fintype.card_fin` potentially unreachable) and is a gauntlet boss that concatenates earlier levels without novel integration. Several levels also suffer from low interactivity — they are one-shot `exact` levels that teach "here is a lemma, use it" without requiring the learner to think about proof structure.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | `Set.mem_univ` used in boss but never introduced. `Fintype.card_fin` from a non-prerequisite world. |
| 2. Granularity fit | 2 | L01, L02, L03 are one-shot `exact` levels with no proof structure. Boss is a gauntlet. |
| 3. Proof-move teaching | 2 | Only L04 teaches a proof move (rewrite-then-close). L01-L03 and L05 are `exact`-only. |
| 4. Inventory design | 2 | `Set.mem_univ` used in boss but never declared as `NewTheorem`. `Fintype.card_fin` not in inventory from this world's dependency chain. Missing `TheoremDoc` for `Set.mem_univ`. |
| 5. Hint design and recoverability | 3 | Hints are layered (visible strategy + hidden code). L04 and L06 have good multi-step hint chains. L01-L03 are so trivial that hints are barely needed. |
| 6. Worked example -> practice -> transfer -> boss | 2 | No practice levels. No transfer. Boss is a gauntlet concatenation. The world goes Introduction x3 -> one conversion -> one rewrite chain -> boss. |
| 7. Mathematical authenticity | 3 | The three-way comparison tables are excellent. The "when to use which" guide in L05 conclusion is genuinely useful. Transfer language in conclusions is solid. |
| 8. Paper-proof transfer | 3 | "In plain language" sections are consistently present and good. The pipeline diagrams in L04 and L06 conclusions are helpful. |
| 9. Technical fit and maintainability | 3 | Compiles cleanly. `DisabledTactic` is consistent across all 6 levels. Missing `TacticDoc` warnings are systemic (pre-existing). |

**Average: 2.4 — Below threshold (needs >= 3.0 with no category below 2).**

---

## 3. Coverage Gaps

### 3a. `Set.mem_univ` — hidden prerequisite leak (P0)

The boss (L06) requires `Set.mem_univ x` to close Part 1. This theorem is never:
- Declared as a `NewTheorem` anywhere in the course
- Given a `TheoremDoc`
- Introduced in any preceding level

The learner encounters it for the first time inside the boss, which violates the "bosses integrate, never introduce" principle. The hints tell the learner to use it, but there is no inventory entry for it.

**Fix**: Add a level before the boss that introduces `Set.mem_univ` with a `NewTheorem` declaration and `TheoremDoc`. Alternatively, add `NewTheorem Set.mem_univ` and `TheoremDoc` to L02 (where `Set.univ` is first discussed) and include a step that uses it.

### 3b. `Fintype.card_fin` — dependency chain gap (P1)

The boss Part 2 requires `Fintype.card_fin`. This theorem is:
- Taught in FintypeClass L04 (direct prerequisite)
- But NOT declared as `NewTheorem` in FintypeClass L04
- Only declared as `NewTheorem` in FinThreeExamples L08, which is NOT on the prerequisite path to ThreeFiniteness

The theorem is available from Mathlib regardless, and the boss hints name it explicitly, so the learner can use it. But it is not in the inventory sidebar unless they happened to complete FinThreeExamples first. This is a discoverability gap.

**Fix**: Either add `NewTheorem Fintype.card_fin` and `TheoremDoc` to FintypeClass L04 (where it's taught), or add it to this world's L05 or a new pre-boss level.

### 3c. No practice or retrieval for `Set.Finite.mem_toFinset` (P2)

`Set.Finite.mem_toFinset` is introduced in L04 and immediately used in the boss (L06). There is no supported practice opportunity between introduction and integration. The learner has used it exactly once before the boss demands it.

### 3d. No practice for `Set.Finite.toFinset_eq_toFinset` (P2)

Similarly introduced in L05 and immediately demanded in the boss.

---

## 4. Granularity Defects

### 4a. L01, L02, L03 are one-shot `exact` levels (P1)

Each of these three levels has the same shape:
- Introduction explains a concept
- Statement requires a single `exact <lemma> _`
- Done

There is no proof structure, no decision-making, no exploration. The learner types one line and moves on. This is pure theorem trivia: "here is a lemma name, type it." The dominant lesson is supposed to be learning the concept, but the level teaches nothing about when or why to use it — only the syntax for applying it.

**Fix**: Make these levels require at least a two-step proof. For example:
- L01: Instead of `{1,2,3}.Finite`, make it `(insert 5 {1,2,3}).Finite` and require `rw [Set.finite_insert]` followed by `exact Set.toFinite _`. This forces engagement with the structure.
- L02: Instead of bare `Set.finite_univ`, require the learner to first use `have : Finite Bool := inferInstance` then `exact Set.finite_univ`. Or set up a goal that requires `Set.finite_univ` as a step in a larger proof.
- L03: Similarly, make the learner do something with the `Set.Finite` proof after obtaining it.

### 4b. Boss is a gauntlet (P1)

The boss has two parts connected by `constructor`:
1. Part 1: `intro x`, `rw [mem_toFinset]`, `exact Set.mem_univ x` — replays L04 with a different closing lemma.
2. Part 2: `rw [toFinset_eq_toFinset]`, `rw [toFinset_univ]`, `rw [card_univ]`, `rw [card_fin]` — extends L05 with two more rewrites.

Neither part requires planning or integration beyond "do what you did before, but with one more step." The conjunction via `constructor` is trivial mechanical glue. There is no novel interaction between the membership and cardinality parts. A gauntlet boss fails taxonomy item #8b.

**Fix**: Redesign the boss to require the learner to combine notions in a way that creates a planning challenge. For example:
- Given `s : Set (Fin 4)` with `hs : s.Finite`, prove `hs.toFinset.card ≤ Fintype.card (Fin 4)`. This requires converting between notions AND reasoning about the relationship.
- Or: prove that `Set.finite_univ.toFinset = Finset.univ` as the main goal (combining L05's technique), then use that equality to derive a cardinality or membership fact. The integration should force the learner to see how the parts fit together, not just replay them in sequence.

### 4c. No transfer level (P2)

The plan calls for L05 as "Practical guidance" (coverage item M35 (S), C1 (R)), implying transfer. But L05 is actually another rewrite-chain level, not a transfer level. There is no level where the learner chooses which finiteness notion to use in a fresh context without being told which lemma to apply. The world introduces three notions and conversion APIs but never asks the learner to make a choice.

---

## 5. Learner Simulation

### 5a. Attentive Novice

**First likely stuck point**: L04. After `rw [Set.Finite.mem_toFinset]`, the goal becomes `1 ∈ insert 1 {2}`. The novice may not know `Set.mem_insert`. The hint says "use `exact Set.mem_insert 1 (singleton 2)` or equivalently `left; rfl`." The `left; rfl` path is accessible (from NNG4). But `Set.mem_insert 1 {2}` requires knowing the exact signature — the notation `{2}` vs `singleton 2` may confuse. **Assessment**: Adequately rescued by the `left; rfl` alternative.

**Most likely wrong move**: In L01, trying `exact Set.finite_singleton _` directly (without `rw [Set.finite_insert]` first). The intro mentions both `Set.finite_singleton` and `Set.finite_insert`, and a novice may try the simpler-looking one first. When it fails, the hint should guide them. **Assessment**: Hints handle this — the first hint mentions `rw [Set.finite_insert]`.

**Whether hints rescue well**: For L01-L03, the visible hints essentially give the answer (`exact <lemma> _`). This is fine for one-shot levels but it means the hints ARE the level — there's nothing to discover. For L04, the hint layering is better: strategy first, then code.

**Whether the lesson is legible**: The comparison tables in L02 and L03 are excellent. The learner will understand the conceptual distinctions. But the levels don't test understanding — they only test the ability to type a lemma name.

### 5b. Experienced Lean User

**Avoidable friction**: The experienced user will find L01-L03 trivially boring. Each is a single `exact`. They will also know that `simp` closes everything and will be mildly annoyed it's disabled. But this is appropriate gating.

**Alias gaps**: After the `rw [Set.Finite.mem_toFinset]` step in L04, the experienced user might try `exact mem_insert_self 1 {2}` or `simp` (disabled). The `Set.mem_insert` path is the only option documented. `mem_insert_self` is not mentioned. This is acceptable but could be noted in a hidden hint.

**Inventory clutter**: No issue. The world introduces a reasonable number of items (6 theorems, 2 definitions across 6 levels).

**Needless forced verbosity**: L06 Part 2 requires four consecutive `rw` steps. An experienced user would prefer `rw [toFinset_eq_toFinset, toFinset_univ, card_univ, card_fin]` as a single call. The game should accept this. Since `rw` accepts a list, this works syntactically, but the hints guide one-at-a-time. **Assessment**: Fine — the one-at-a-time guidance serves the novice; the experienced user can combine them.

---

## 6. Boss Integrity Notes

### Required checks for the boss (L06):

| Check | Result | Notes |
|-------|--------|-------|
| Seeded subskills | FAIL | `Set.mem_univ` is unseeded — never introduced before the boss. |
| Closure quality | FAIL | `Set.Finite.mem_toFinset` has only 1 use before the boss (L04). `toFinset_eq_toFinset` has 1 use (L05). Zero retrieval. |
| Integration quality | FAIL | Gauntlet — two independent parts glued by `constructor`. No novel interaction. |
| Surprise burden | MARGINAL | The 4-step rewrite chain in Part 2 is longer than anything practiced, but each step is guided by hints. |
| Can learner explain why? | YES | The conclusion's pipeline diagram makes the proof logic clear. |

---

## 7. Technical Risks

| Issue | Severity | Notes |
|-------|----------|-------|
| `Set.mem_univ` not in inventory | P0 | Used in boss but never declared as `NewTheorem` or documented with `TheoremDoc`. Hidden prerequisite. |
| `Fintype.card_fin` not in direct dependency chain's inventory | P1 | Declared in FinThreeExamples but ThreeFiniteness doesn't depend on it. Available from Mathlib but not in sidebar. |
| Missing `TacticDoc` warnings for disabled tactics | P2 (systemic) | `trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all` all produce "Missing Tactic Documentation" build info messages. Pre-existing systemic issue, not new to this world. |
| No `TheoremTab` except in boss | P2 | L01-L05 don't set a `TheoremTab`. The theorems (in "Set" tab per docs) may not be easily findable by the learner in earlier levels. |
| L05 `simp` on the equation `Set.finite_univ.toFinset = Finset.univ` partially works | P2 (blocked) | `simp` gets the goal to `{false, true} = {true, false}` but can't close it. Since `simp` is disabled, this is blocked. No risk. |

---

## 8. Ranked Patch List

| # | Severity | Issue | Fix |
|---|----------|-------|-----|
| 1 | **P0** | `Set.mem_univ` used in boss but never introduced | Add a pre-boss level (or add to L02) that introduces `Set.mem_univ` with `NewTheorem` and `TheoremDoc`. Must be introduced AND practiced before the boss uses it. |
| 2 | **P1** | Boss is a gauntlet (concatenation, no novel integration) | Redesign boss to require a planning challenge that combines membership and cardinality reasoning in a non-sequential way. See Section 4b for suggestions. |
| 3 | **P1** | L01, L02, L03 are trivial one-shot `exact` levels | Redesign to require at least two tactic steps each, forcing engagement with the concept rather than just the lemma name. See Section 4a for suggestions. |
| 4 | **P1** | `Fintype.card_fin` not declared as `NewTheorem` in FintypeClass | Add `NewTheorem Fintype.card_fin` and `TheoremDoc Fintype.card_fin` to FintypeClass L04 (or to a level in this world before the boss). |
| 5 | **P2** | No practice levels between introductions and boss | Add at least one supported practice level where the learner uses `Set.Finite.mem_toFinset` or `toFinset_eq_toFinset` in a slightly different context before the boss demands them. |
| 6 | **P2** | No transfer level | Add a level where the learner must choose which finiteness notion to use (e.g., given a goal, decide whether to work with `Set.Finite`, `Fintype`, or `Finset`). |
| 7 | **P2** | `TheoremTab` only on boss | Add `TheoremTab "Set"` to L01 (or whichever is the first level introducing Set theorems) so the theorem panel is organized from the start. |

---

## 9. What to Playtest Again After Patching

1. **All levels if L01-L03 are redesigned**: New proof structures need exploit checking, hint verification, and learner simulation.
2. **Boss after redesign**: Verify the new boss is not a gauntlet, that all subskills are seeded, and that no new hidden prerequisites are introduced.
3. **Any new practice/transfer levels**: Standard R2 audit.
4. **Exploit check on any new statements**: Verify `simp`, `trivial`, `decide`, `omega`, `norm_num` are still blocked on all new levels.
5. **Inventory coherence after adding `Set.mem_univ`**: Make sure it appears in the right `TheoremTab` and has a clear `TheoremDoc`.
