# Playtest Audit: W3 ListBasics

**Auditor**: playtest-auditor (adversarial)
**World**: W3 — Lists: construction and operations
**World type**: Lecture
**Levels audited**: L01 through L08 (8 levels)
**Build status**: Compiles (verified)

---

## 1. Overall Verdict

**FAILING.** The world compiles but is pedagogically hollow. Every single level (including the boss) is solved by a single invocation of `decide` or `simp` on a fully concrete statement. There are zero proof moves taught, zero tactic decisions required, zero moments where the learner must think about structure rather than press a button. The boss is a fake boss (taxonomy defect #8) — it is solved by `decide` in one step, identical to every non-boss level. The world is a tour of `List` API names rather than a teaching instrument.

Additionally, the implemented level order and content deviate from the plan (missing `List.Nodup`, added `List.reverse`, reordered levels), and the plan's own coverage item M17 (`List.Nodup`) — the setup for the entire next world (W4 Multisets) — is absent.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 1 | M17 (`List.Nodup`) missing entirely. No proof-move coverage at all. No retrieval, no integration. |
| 2. Granularity fit | 1 | Every level has the same shape: concrete equality/membership proved by `decide`/`simp`. No variation in difficulty or proof structure. |
| 3. Proof-move teaching | 0 | Zero proof moves taught. No `intro`, no `cases`, no `induction`, no `rw`, no `have`, no structural reasoning. Every level is automation. |
| 4. Inventory design | 2 | Definitions are introduced with `NewDefinition`. `simp` and `decide` are introduced as `NewTactic` in L02. But the inventory is effectively unused — the learner never needs to think about what tool to reach for. |
| 5. Hint design and recoverability | 1 | Every hint says "try `decide`" or "try `simp`". No strategy hints. No rescue for wrong paths. No layered hints. Hints are uniform spoilers. |
| 6. Worked example -> practice -> transfer -> boss | 0 | No progression exists. L01 through L07 are all identical in difficulty and proof shape. The boss (L08) is the same. There is no scaffolding fade, no independence development. |
| 7. Mathematical authenticity | 2 | Introductions and conclusions are well-written and mathematically accurate. Transfer moments in conclusions are present ("In plain language..."). But the exercises themselves never engage with the math — the learner reads about it but never does it. |
| 8. Paper-proof transfer | 2 | Conclusions contain good "in plain language" translations. But since the proofs are all `decide`, the learner has no proof structure to transfer. |
| 9. Technical fit and maintainability | 2 | Compiles. Dependencies are sane. But the world deviates from the plan. |

**Average: 1.2.** Below the threshold of 3.0. Multiple categories at 0 or 1. **Red flags triggered**: fake boss, no proof-move teaching, missing coverage for M17, boss depends on no integration at all.

---

## 3. Coverage Gaps

### 3a. Plan vs. Implementation Mismatch

The plan specifies this level order:

| Plan # | Plan level | Implemented as |
|--------|-----------|----------------|
| 1 | `cons` and empty list | L01 (match) |
| 2 | List membership | L03 (reordered to position 3) |
| 3 | `List.length` | L02 (reordered to position 2) |
| 4 | `List.append` | L06 (reordered to position 6) |
| 5 | `List.map` | L04 (reordered to position 4) |
| 6 | `List.filter` | L05 (reordered to position 5) |
| 7 | **`List.Nodup`** | **MISSING** |
| 8 | Boss | L08 (match, but content differs) |

**Added level not in plan**: L07 (`List.reverse`) replaces the planned `List.Nodup` level.

### 3b. Missing Coverage Items

| Item | Axis | Status | Impact |
|------|------|--------|--------|
| M17 (`List.Nodup`) | MATH | **Missing entirely** | P0. This is the bridge to W4 (Multisets). The plan lists it as M17 (I) — first introduction. Without it, the learner arrives at the Multiset world never having seen `Nodup`, which is central to understanding how `Multiset -> Finset` works. |
| N11 (`::` notation) | NOTATION | Introduced but never practiced structurally | P2. The learner sees `::` in L01 but never has to use it in a proof where automation doesn't work. |
| N12 (`++` notation) | NOTATION | Introduced in L06 but never practiced | P2. Same issue. |

### 3c. Proof-Move Coverage (Catastrophic Gap)

The plan maps these proof moves to W3:

| Move | Plan status | Actual status |
|------|------------|---------------|
| V1 (unfolding a definition) | Should be reviewed from W1 | Never exercised. All levels use automation. |
| V18 (`have` for subgoals) | Should be reviewed from W1 | Never exercised. |

The world teaches **zero** proof moves. The learner enters knowing `rw`, `exact`, `apply`, `intro`, `cases`, `constructor`, `have`, `use`, `assumption` (NNG4 baseline) and exits having used none of them. This is a pure regression in proof skill.

### 3d. Example Coverage

All examples are concrete and well-chosen (specific lists with specific elements). This is fine. But the learner never engages with them beyond pressing `decide`.

### 3e. Transfer Coverage

Conclusions contain good "in plain language" summaries. But transfer requires the learner to have *done* something they can transfer. Since they did nothing, there is nothing to transfer.

---

## 4. Granularity Defects

### 4a. Overfine: All non-boss levels are structurally identical (Taxonomy #3)

L01 through L07 all share the same proof shape:
1. Read a concrete goal about a concrete list
2. Type `decide` (or `simp` or `rfl`)
3. Done

The only variation is which `List` API function appears in the statement. This is the definition of "differs only by superficial renaming" from the failure taxonomy. Seven levels that all teach the same non-lesson.

**Severity**: P1. The levels are not individually harmful, but collectively they waste the learner's time without building any skill.

### 4b. Boss is a single-step concrete computation (Taxonomy #8: Fake Boss)

The boss statement is:
```lean
3 ∈ ([1, 2, 3] ++ [4, 5] : List Nat).reverse
```

This is solved by `decide` in one step. The plan says the boss should "combine `map`, `filter`, `length`, and membership in one proof" — but the actual boss combines only `append`, `reverse`, and `membership`, and the "combination" is illusory because `decide` evaluates the entire expression without the learner having to decompose it.

A real boss would require the learner to:
- Break the problem into subgoals using `have`
- Apply multiple API lemmas manually
- Handle an intermediate computation where automation doesn't reach

**Severity**: P0 (blocking). The boss is a fake boss.

### 4c. No difficulty progression

Every level has the same difficulty: trivial. There is no ramp from easy to hard. The boss is no harder than L01. This violates the progression requirement (rubric category 6).

---

## 5. Statement Exploitability (1b)

### Systematic exploit: Every level is solvable by `decide`

| Level | Statement | Intended proof | Exploit | Severity |
|-------|-----------|----------------|---------|----------|
| L01 | `[1, 2, 3] = (1 :: 2 :: 3 :: [] : List Nat)` | `rfl` | `decide` | P2 (intended `rfl` is fine, but `decide` also works — acceptable) |
| L02 | `[10, 20, 30].length = 3` | `simp` | `decide` | P1 (both are one-shot, no learning) |
| L03 | `2 ∈ [1, 2, 3]` | `decide` | `decide` is the intended proof | P1 (nothing is taught) |
| L04 | `List.map (· * 2) [1, 2, 3] = [2, 4, 6]` | `decide` | `simp`, `native_decide` | P1 |
| L05 | `List.filter (fun x => decide (x < 4)) [1, 2, 3, 4, 5] = [1, 2, 3]` | `decide` | `simp` | P1 |
| L06 | `([1, 2] ++ [3, 4, 5] : List Nat).length = 5` | `simp` | `decide` | P1 |
| L07 | `[1, 2, 3, 4].reverse = [4, 3, 2, 1]` | `decide` | `simp` | P1 |
| L08 | `3 ∈ ([1, 2, 3] ++ [4, 5] : List Nat).reverse` | `decide` | `simp` | P0 (boss) |

**The core problem**: Every statement is a fully concrete decidable proposition. There are no universally quantified statements, no symbolic lists, no hypotheses to work with. The learner never needs to engage with proof structure because the statements have no structure.

**Contrast with what would work**: A level like "Given `h : a ∈ l`, prove `a ∈ l ++ m`" requires the learner to use `List.mem_append.mpr` or `Or.inl` — it has proof structure. A level like "Prove `(List.map f l).length = l.length` by induction on `l`" requires actual proof moves. The current levels have none of this.

---

## 6. Interactive Proof Quality (1c)

Every level is a one-step proof. There is no interactive proof experience. The learner types a single tactic and the level ends. There are no intermediate goal states to inspect, no decisions to make, no moments of discovery.

This is the most severe form of interactive proof quality failure: **there is no interaction at all**.

---

## 7. Learner Simulation

### 7a. Attentive Novice

**Profile**: Completed NNG4. Comfortable with `rw`, `exact`, `apply`, `intro`. New to lists.

**Experience of the world**:
1. Opens L01. Reads the introduction (good, explains `::` and `[]`). Sees goal: `[1, 2, 3] = 1 :: 2 :: 3 :: []`. Types `rfl`. Done in 5 seconds.
2. Opens L02. Reads about `List.length`. Goal: `[10, 20, 30].length = 3`. Tries `simp`. Done.
3. Opens L03. Reads about `List.Mem`. Goal: `2 ∈ [1, 2, 3]`. Tries `decide`. Done.
4. Pattern recognition kicks in: "Every level is solved by `decide` or `simp`."
5. L04-L07: Skims introduction, types `decide`, moves on. Reading becomes optional.
6. Boss (L08): Types `decide`. World complete.

**First stuck point**: None. The novice is never stuck. This sounds good but is actually terrible — it means the world offers no resistance, no moment of productive struggle, no learning.

**Most likely wrong move**: None that wouldn't also work.

**Hint quality**: The novice never needs hints because the levels are trivial. The hints are untestable.

**Lesson legibility**: The novice learns that lists exist and have certain operations. They learn this from reading the introductions, not from doing proofs. The same knowledge could be acquired from reading documentation.

**What the novice does NOT learn**: How to reason about lists in a proof. How to use `List.mem_cons` to decompose membership. How to do induction on a list. How to connect list operations to each other. How to build a proof that involves lists as part of a larger argument.

### 7b. Experienced Lean User

**Profile**: Comfortable with Lean 4. Has used lists before. Taking this course for finite math content.

**Experience**:
1. Opens L01. Sees `rfl`. Types `rfl`. "Okay, warmup."
2. L02-L07: Types `decide` for each without reading. Takes approximately 90 seconds total.
3. Boss: `decide`. "That was a world?"

**Friction points**: None (zero friction is itself a problem — it means zero engagement).

**Assessment**: The experienced user gains nothing. They already know lists exist. They needed practice reasoning about lists in Lean's proof mode, not verifying concrete equalities.

---

## 8. Boss Integrity

### Boss: L08 — "Combining list operations"

**Statement**: `3 ∈ ([1, 2, 3] ++ [4, 5] : List Nat).reverse`

**Required subskills**: None. `decide` evaluates the entire expression.

**Seeded subskills check**:
- The plan says the boss should integrate `map`, `filter`, `length`, and membership.
- The actual boss uses `append`, `reverse`, and membership — but none of these need to be "used" because `decide` handles everything.
- `map` and `filter` are not tested in the boss at all, despite being taught in L04-L05.
- **Verdict**: The plan's boss coverage is not implemented.

**Closure quality**: There is no closure. The boss does not require retrieving anything learned in L01-L07.

**Integration quality**: There is no integration. The boss is a single concrete membership check that happens to involve `append` and `reverse` syntactically.

**Surprise burden**: Zero. The boss is easier than some of the non-boss levels.

**Could the learner explain why the proof works?**: "I typed `decide` and Lean computed the answer." This is not a proof explanation. The learner cannot explain the proof because there is no proof — there is only computation.

**Boss verdict**: **Fake boss** (taxonomy defect #8). The boss must be redesigned.

---

## 9. Course-Role Sanity

The world is labeled as a **Lecture** world. A lecture world should:
- Introduce new concepts
- Provide first-contact with new proof moves
- Include worked examples with visible proof structure
- Build toward a boss that integrates the world's repertoire

The current world:
- Introduces new concepts (via text) -- YES
- Provides first-contact with proof moves -- NO (zero proof moves)
- Includes worked examples with visible proof structure -- NO (all proofs are opaque one-step automation)
- Builds toward an integrative boss -- NO (boss is identical to non-boss levels)

**Role assessment**: The world functions as a **glossary**, not a lecture. It tells the learner about list operations but never requires them to do anything with that knowledge.

---

## 10. Technical Risks

| Risk | Severity | Detail |
|------|----------|--------|
| Plan deviation: level order changed | P2 | Membership moved from #2 to #3, length from #3 to #2, append from #4 to #6. Minor but should be documented. |
| Plan deviation: `List.Nodup` (L07 in plan) replaced by `List.reverse` | P0 | M17 is a critical bridge to W4. Its absence means W4's first level will need to introduce `Nodup` cold. |
| Plan deviation: Boss content differs from plan | P1 | Plan says boss uses `map`, `filter`, `length`, membership. Actual boss uses `append`, `reverse`, membership. |
| `import Mathlib` in every level file | P2 | Compiles but is heavyweight. Consider importing only needed modules. |
| No `DisabledTactic` or `DisabledTheorem` usage | P1 | Without gating, `simp`, `decide`, and `native_decide` are all available and close every level trivially. |

---

## 11. Ranked Patch List

### P0 (Blocking — must fix before the world is shippable)

1. **Redesign all statements to require structural proofs.** The core defect is that every statement is a fully concrete decidable proposition. At least half the levels must involve universally quantified statements, symbolic lists (variables, not literals), or hypotheses that require the learner to use API lemmas manually. Examples:
   - "Given `a ∈ l`, prove `a ∈ a :: l`" (requires `List.mem_cons.mpr` or `Or.inl`)
   - "Prove `(l₁ ++ l₂).length = l₁.length + l₂.length`" by induction
   - "Given `a ∈ l` and `f : α → β`, prove `f a ∈ List.map f l`" (requires `List.mem_map.mpr`)
   - "Given `a ∈ l` and `p a = true`, prove `a ∈ List.filter p l`" (requires `List.mem_filter.mpr`)

2. **Gate `decide` and `simp` for levels that should require manual reasoning.** Use `DisabledTactic` to block `decide` (and possibly `simp`) on levels where the dominant lesson is a specific API lemma or proof move. Re-enable them selectively where the lesson is specifically about using automation.

3. **Add the missing `List.Nodup` level.** This is M17 (I) in the plan and is the critical bridge to W4 (Multisets). It should be a level where the learner proves a concrete list has no duplicates AND a level where they see a list that does have duplicates, setting up the `Nodup` property for multisets.

4. **Redesign the boss to require genuine integration.** The boss should require at least 3 distinct moves from the world's repertoire, with a planning challenge that goes beyond replaying individual levels. Example: "Given a list `l`, prove that `(List.map f (List.filter p l)).length ≤ l.length`" — this requires combining knowledge of `map`, `filter`, and `length` in a way that forces structural reasoning.

### P1 (High — should fix)

5. **Add at least one level with `intro` or `cases` on list structure.** The learner should have at least one level where they case-split on `l = [] | l = a :: t`, or introduce a universally quantified variable. This previews induction without requiring it.

6. **Add layered hints.** Replace the uniform "try `decide`" hints with:
   - Strategy hint (visible): "Think about what `append` does — it puts all elements of the first list before all elements of the second."
   - Tactic hint (hidden): "Try `rw [List.append_assoc]` to simplify."
   - Rescue hint (hidden): "If stuck, `simp [List.mem_append]` can help."

7. **Add at least one level where the learner must use `rw` with a list lemma.** For example, rewriting with `List.length_append` or `List.length_map`. This exercises the proof-move layer and connects to NNG4 baseline skills.

8. **Align boss content with the plan.** The boss should test `map`, `filter`, `length`, and membership — not just `append` and `reverse`.

### P2 (Medium — nice to fix)

9. **Re-evaluate inclusion of `List.reverse`.** `List.reverse` is not in the plan's coverage map. It is not used in any later world. Either add it to the plan with justification or replace L07 with the planned `List.Nodup` level.

10. **Add a difficulty progression.** Early levels should be simpler (concrete, one operation). Later levels should combine operations and require multi-step proofs. The boss should be noticeably harder than any individual level.

11. **Add more substantive transfer moments.** The conclusions mention "in plain language" translations, which is good. But add at least one level where the *statement* itself is a transfer exercise — e.g., "State in words what `a ∈ List.map f l` means."

---

## 12. What to Playtest Again After Patching

After implementing the patches above, the following require re-audit:

1. **All redesigned levels** — verify that the new statements actually require the intended proof moves and cannot be trivially closed by automation.
2. **The boss** — verify it requires genuine integration of 3+ skills, is not solvable by `decide`, and has appropriate hint coverage for stuck learners.
3. **The `List.Nodup` level** — verify it properly sets up M17 for W4.
4. **Tactic gating** — verify that `DisabledTactic` is applied correctly and that the intended proof paths work while the unintended ones are blocked.
5. **Learner simulation** — re-simulate the attentive novice to verify they encounter productive struggle and learn proof moves, not just API names.
6. **Coverage closure** — verify M16 and M17 both reach at least (S) state, and that the boss achieves (G) for M16.

---

## Summary of Defects by Taxonomy

| Taxonomy # | Defect | Where |
|-----------|--------|-------|
| #3 Overfine | L01-L07 all have identical proof shape | Entire world |
| #4 Surface coverage only | Every API item is introduced but never practiced structurally | M16, N11, N12 |
| #6 Spoiler hint | Every hint gives the exact tactic immediately | All levels |
| #8 Fake boss | Boss solved by `decide` in one step | L08 |
| #12 Syntax dominates math | Learner learns API names but no proof structure | Entire world |

---

## Final Assessment

This world needs a complete rewrite of its proof-level content. The introductory text and conclusions are well-written and should be preserved. But the statements, proofs, hints, and boss must be redesigned from scratch to create genuine learning experiences. The world should teach the learner to *reason about lists in proofs*, not merely to *recognize list API function names*.

The `List.Nodup` gap is a structural problem that will cascade into W4 if not fixed.

Until these issues are resolved, the world should not be considered complete.
