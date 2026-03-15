# W6 FinsetMembership -- Playtest Audit R1

## 1. Overall Verdict

**Needs revision.** The world is well-structured pedagogically with a clear three-act progression (manual rewriting -> simp automation -> destructuring), but has two P0 exploitability issues (`norm_num` bypasses L01-L03 entirely, and `fin_cases` bypasses L08's rcases lesson) plus several P1/P2 issues around missing disabled tactics and boss integrity.

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 3 | Good coverage of membership lemma family; missing `Finset.not_mem_empty` |
| 2. Granularity fit | 3 | Each level has a clear dominant lesson; L04 and L05 are close in purpose |
| 3. Proof-move teaching | 3 | Manual search pattern is well-taught; `rw [...] at h` + `rcases` pattern is clear |
| 4. Inventory design | 2 | `norm_num` and `fin_cases` not disabled; `simp` first contact in this world but declared NewTactic in prior world |
| 5. Hint design and recoverability | 3 | Good layering (strategy -> hidden code) throughout; L09 boss has thorough per-step hints |
| 6. Progression (demo -> practice -> transfer -> boss) | 3 | Clear L01-L03 -> L04-L05 -> L06-L08 -> L09 progression |
| 7. Mathematical authenticity | 3 | Good explanations of why finsets have no duplicates; good comparison to lists |
| 8. Paper-proof transfer | 3 | Every level has a "In plain language" block; conclusion has transfer section |
| 9. Technical fit | 2 | Build succeeds but has info-level warnings about missing TacticDocs; exploit paths open |

**Average: 2.8** -- below the 3.0 threshold for "good." Inventory design and technical fit need fixes.

## 3. Coverage Gaps

### Covered well:
- `Finset.mem_insert` (I: L01, S: L02-L03, R: L08, G: L09)
- `Finset.mem_singleton` (I: L03, S: L04-L05, R: L08, G: L09)
- `simp` with lemma list (I: L04, S: L05-L07, G: L09)
- `Finset.insert_eq_of_mem` (I: L06, G: L09)
- `rw [...] at h` (I: L08, G: L09)
- `rcases h with rfl | h` (I: L08, G: L09)

### Gaps:
1. **`Finset.not_mem_empty`** -- never mentioned. If a learner peels all insert layers and reaches `∅`, they have no lemma. The L03 proof terminates at `mem_singleton` rather than reaching the empty finset, so this is not blocking, but it is a gap for the next world (union/intersection may produce empty finsets).
2. **`simp` without a lemma list** -- L04 always passes explicit lemmas to `simp`. The fact that bare `simp` might also close these goals (via `@[simp]`-tagged lemmas) is never discussed. P2 concern -- this is fine for now but may cause confusion later when learners try `simp` without arguments.
3. **`Finset.mem_cons`** -- the predecessor world taught `cons` (W7 L05), but this world only uses `insert`. The connection between `cons` membership and `insert` membership is never made. Low priority.

## 4. Granularity Defects

### L04 vs L05 -- close in purpose
L04 introduces `simp [mem_insert, mem_singleton]` on `2 ∈ {1,2,3}`. L05 uses the same technique on `3 ∈ insert 1 (insert 2 {3,4})`. The dominant lesson of both is "use simp with membership lemmas." L05's stated purpose is "simp vs manual rewriting" but the level only uses simp -- there is no actual comparison in the proof. The "comparison" is entirely in the prose.

**Severity**: P2. The level works, but the title/intro promise ("solve the same goal both ways") is not fulfilled by the proof task. The learner is only asked to use simp, not to compare approaches.

**Suggested fix**: Either (a) make L05 require the learner to prove the goal twice (once manually, once with simp) using `And.intro` or a conjunction, or (b) rename L05 to "simp on a deeper finset" and adjust the intro text to match what the level actually does.

### L07 -- thin level
L07 teaches non-membership but the proof is a single `simp` call. There is no new proof move beyond what L04-L05 already taught. The only new concept is the `∉` notation, which is explained in the intro but not exercised as a distinct proof challenge.

**Severity**: P2. The level is not wrong, but it could be enriched by either (a) requiring the manual approach (with `intro h` then case analysis) to practice the `rw [...] at h` pattern that L08 will need, or (b) combining it with a membership fact into a conjunction to add substance.

## 5. Statement Exploitability -- P0 Issues

### E1 (P0): `norm_num` bypasses L01-L03 entirely

**Affected levels**: L01, L02, L03, L06, L07, L09 (Parts A and C)

`norm_num` is taught in FinCompute W2 and is NOT disabled in any FinsetMembership level. Testing confirms:
- `norm_num` closes `1 ∈ ({1, 2, 3} : Finset Nat)` (L01)
- `norm_num` closes `2 ∈ ({1, 2, 3} : Finset Nat)` (L02)
- `norm_num` closes `3 ∈ ({1, 2, 3} : Finset Nat)` (L03)
- `norm_num` closes `insert 2 ({1,2,3} : Finset Nat) = {1,2,3}` (L06)
- `norm_num` closes `4 ∉ ({1,2,3} : Finset Nat)` (L07)
- `norm_num` closes L09 Parts A and C

L01-L03 specifically disable `simp` to force manual rewriting with `mem_insert` and `mem_singleton`. But `norm_num` completely bypasses this. The learner can pass L01-L03 with a single `norm_num` call, learning nothing about the membership lemma family.

**Fix**: Add `norm_num` to `DisabledTactic` on L01-L03 (and arguably on L06 where the lesson is `insert_eq_of_mem`, not automation).

### E2 (P0): `fin_cases` bypasses L08's rcases lesson

**Affected levels**: L08, L09 (Part B)

`fin_cases` is taught in FinCompute and is available. Testing confirms:
- `fin_cases h <;> omega` closes L08 in one line
- `fin_cases hx <;> simp [Finset.mem_insert, Finset.mem_singleton]` closes L09 Part B

L08's entire purpose is to teach `rw [Finset.mem_insert] at h` + `rcases h with rfl | h` as a proof pattern for symbolic membership. `fin_cases` does exactly the same thing automatically. The learner can pass L08 without ever using `rcases` or `rw [...] at h`.

**Fix**: Add `fin_cases` to `DisabledTactic` on L08 and L09. The learner should use the manual destructuring pattern here; `fin_cases` can remain available in later worlds where it is appropriate.

### E3 (P1): `simp [...] at h` + `omega` bypasses L08's rcases lesson

Even with `fin_cases` disabled, the learner can use `simp [Finset.mem_insert, Finset.mem_singleton] at h` to destructure `h` into a disjunction, then `omega` to close all cases. This is a two-step proof that bypasses `rcases` entirely.

**Severity**: P1 (not P0). The learner still learns something (`simp` at hypotheses, `omega` for arithmetic), and the two-step structure requires understanding the proof state. But it bypasses the intended `rcases` lesson.

**Fix options**:
(a) Disable `simp` on L08 (reverting to the L01-L03 style). This forces `rw [...] at h` + `rcases`.
(b) Accept as P1 -- the `simp at h` approach is a legitimate alternative that the learner might discover, and it still teaches membership reasoning.

**Recommendation**: Option (a) is cleaner. L08 should disable `simp` so the learner must use `rw [...] at h` + `rcases`. The conclusion can note that `simp` could also destructure membership hypotheses.

### E4 (P2): `simp` closes L09 Parts A and C without teaching anything new

Parts A and C of the boss can be closed by `simp [Finset.mem_insert, Finset.mem_singleton]` or `norm_num` without using `insert_eq_of_mem` or understanding idempotency. This means the boss only tests Part B for the `rcases` pattern.

**Severity**: P2 (given that norm_num and fin_cases are fixed). With `norm_num` disabled and `fin_cases` disabled, Part A still requires `insert_eq_of_mem` + `simp` (the intended proof), and Part B requires `rw [...] at h` + `rcases`. This is acceptable integration.

## 6. Interactive Proof Quality

### L08 -- deep nesting
The intended proof of L08 is 8 tactic steps with nested bullet points:
```
rw [Finset.mem_insert] at h
rcases h with rfl | h
· omega
· rw [Finset.mem_insert] at h
  rcases h with rfl | h
  · omega
  · rw [Finset.mem_singleton] at h
    rcases h with rfl
    omega
```

This is deeply nested (3 levels of bullets) and somewhat mechanical. However, each step produces visible feedback in the goal state, and the pattern is well-hinted. The depth is inherent to the task (3-element finset = 3 cases). **Acceptable.**

### L09 -- boss length
The boss proof is approximately 20 tactic steps. This is the longest proof in the world by a significant margin (L08 is 8 steps, everything else is 1-3 steps). The jump from L08 to L09 is significant but not unreasonable -- the boss integrates familiar techniques.

However, the three-part conjunction structure means the learner must navigate `constructor` twice, plus the deeply nested Part B. This is a lot of mechanical work. **P2: Consider whether Part A could be simplified to reduce total proof length without sacrificing integration quality.**

## 7. Learner Simulation

### Attentive Novice

**First stuck point**: L01 -- the novice may not immediately recognize that `{1, 2, 3}` desugars to `insert 1 (insert 2 {3})`. The intro explains this, but the novice must read carefully. The first hint reinforces it. **Rescue: good.**

**Most likely wrong move**: L02 -- the novice may try `left` after the first `rw [Finset.mem_insert]`, not recognizing that `2 = 1` is false. The hints correctly guide to `right`. **Rescue: good.**

**L08 stuck point**: The `rfl` pattern in `rcases h with rfl | h` is genuinely new and surprising. The novice has used `rcases` before (ListBasics L10) but may not know the `rfl` substitution pattern. The intro and hints explain it well. **Rescue: adequate but could be stronger** -- a hidden hint showing the exact `rcases h with rfl | h` syntax after the strategy hint would help.

**Boss (L09)**: The three-part structure may overwhelm. The novice might not realize they need `constructor` to split the conjunction, especially since the last level (L08) didn't use `constructor`. The first hint says to split with `constructor`, which rescues this. **Rescue: good.**

### Experienced Lean User

**Avoidable friction**: The experienced user will want to use `decide`, `norm_num`, or `fin_cases` throughout. All three bypass the lessons. With the recommended fixes (disable `norm_num` on L01-L03, disable `fin_cases` on L08-L09), the experienced user will be mildly annoyed but will understand the pedagogical intent.

**`simp` on L04-L05**: The experienced user will find L04 and L05 trivially easy (single `simp` call each). This is fine -- these are first-contact levels for `simp` with finset lemmas, and the experienced user will appreciate the brevity. But L05 in particular adds nothing for an experienced user.

**Missing alias**: The experienced user might try `Finset.mem_insert.mpr` or `Or.inl` / `Or.inr` instead of `left`/`right`. These should work if available. Not a problem.

**Inventory clutter**: Three new theorems (`mem_insert`, `mem_singleton`, `insert_eq_of_mem`) and one new tactic (`rcases`) are introduced. This is reasonable for 9 levels.

## 8. Boss Integrity (L09)

### Seeded subskills:
- `constructor` for conjunction splitting -- used since NNG4, not new. **Seeded: yes.**
- `Finset.insert_eq_of_mem` -- introduced in L06. **Seeded: yes.**
- `simp [mem_insert, mem_singleton]` -- introduced in L04. **Seeded: yes.**
- `rw [...] at h` + `rcases h with rfl | h` -- introduced in L08. **Seeded: yes, but only one level of practice before boss.**
- `omega` for arithmetic -- available since FinIntro. **Seeded: yes.**

### Closure quality:
The `rw [...] at h` + `rcases` pattern is introduced in L08 and immediately used in the boss. There is only ONE practice level (L08) before the boss requires it. This is thin but not blocking, since L08 provides thorough coaching for the exact same pattern.

### Integration quality:
The boss requires three different techniques (idempotency via `insert_eq_of_mem`, containment via `rcases`, non-membership via `simp`). This is genuine integration, not mere concatenation. Part B especially requires combining `rw [...] at h` + `rcases` with `simp` in a way not seen in any single prior level.

### Gauntlet check:
Part A is L06 repeated with two inserts instead of one. Part C is L07 repeated. Part B is L08 applied to a different finset pair. The boss is close to the gauntlet boundary: each part closely mirrors a specific prior level. The integration comes from combining all three in one proof. **P2: borderline gauntlet.** The boss would be stronger if Part B required a novel interaction (e.g., proving a property that requires both membership verification AND destructuring in the same chain).

## 9. Course-Role Sanity

This is a **LECTURE** world. The progression from first-contact (L01-L03) through introduction of automation (L04-L05) to practice (L06-L07) to new technique (L08) to boss (L09) is appropriate for a lecture world.

However, the world's promise ("The learner can prove membership goals using `simp` with finset lemmas, and understands that `insert` is idempotent") understates the L08 contribution. Destructuring membership hypotheses (`rw [...] at h` + `rcases`) is a significant proof move that deserves mention in the world promise.

## 10. Technical Risks

1. **Build warnings**: L08 triggers "Missing Tactic Documentation" info messages for `trivial`, `decide`, `native_decide`, `aesop`, `simp_all`. These are non-blocking (falls back to existing docstrings) but should be cleaned up.

2. **Duplicate NewTactic**: L08 declares `NewTactic rcases`, but `rcases` was already declared in ListBasics L10. This may cause the game server to re-announce `rcases` as new. Check whether this is the desired behavior or if it should be removed.

3. **i18n translation warning**: L08 conclusion text triggers a "No translation found" warning for the `rcases` TacticDoc content. Non-blocking but untidy.

## 11. Ranked Patch List

### P0 (Blocking)

**P0-1: Add `norm_num` to DisabledTactic on L01, L02, L03**
`norm_num` closes all three levels with a single call, completely bypassing the manual `rw [Finset.mem_insert]` / `left` / `right` / `rfl` pattern that is the entire pedagogical purpose of these levels. Without this fix, the world's first three levels teach nothing.

**P0-2: Add `fin_cases` to DisabledTactic on L08 and L09**
`fin_cases h <;> omega` closes L08 in one line, bypassing the intended `rw [...] at h` + `rcases` lesson. `fin_cases hx <;> simp [...]` similarly bypasses L09 Part B.

### P1 (High)

**P1-1: Add `norm_num` to DisabledTactic on L06**
`norm_num` closes `insert 2 {1,2,3} = {1,2,3}` without using `insert_eq_of_mem`. The lesson (idempotency via `insert_eq_of_mem`) is bypassed.

**P1-2: Consider disabling `simp` on L08**
`simp [Finset.mem_insert, Finset.mem_singleton] at h; omega` closes L08 without using `rcases`. This bypasses the `rw [...] at h` + `rcases` pattern. Disabling `simp` on L08 forces the manual approach. The conclusion could note that `simp at h` is an alternative.

**P1-3: L05 title/intro mismatch**
The title says "simp vs manual rewriting" and the intro says "Solve the same goal both ways," but the level only asks the learner to use simp. Either change the task to actually require both approaches, or update the title/intro to match the actual task ("simp on a deeper finset").

### P2 (Medium)

**P2-1: Add `norm_num` to DisabledTactic on L07**
`norm_num` closes non-membership without using `simp`. Since L07's purpose is to show `simp` handling non-membership, `norm_num` bypasses the lesson.

**P2-2: Remove duplicate `NewTactic rcases` from L08**
`rcases` is already declared in ListBasics L10. The duplicate declaration may cause the game server to re-announce it. If the intent is to re-introduce it in this context, keep it but add a note in the intro ("You have used `rcases` before...").

**P2-3: Boss borderline gauntlet**
Parts A, B, C each closely mirror specific prior levels (L06, L08, L07). Consider adding a novel integration demand to Part B (e.g., a property requiring both membership construction and destructuring in a single chain rather than sequentially).

**P2-4: L07 thin level**
L07's proof is a single `simp` call. Consider requiring the manual approach (with `intro h`, `rw [...] at h`, etc.) to provide practice for the L08 pattern, or combine with another task for more substance.

**P2-5: Closure gap for `rw [...] at h` + `rcases` before boss**
L08 is the only level teaching the destructuring pattern before the boss requires it. Consider adding one more practice level (e.g., "if x in {10, 20, 30}, then x is even") to strengthen closure.

### P3 (Low)

**P3-1: Add `TacticDoc` entries for disabled tactics if not inherited**
The build shows "Missing Tactic Documentation" info messages. Add `TacticDoc trivial`, `TacticDoc decide`, etc. in L01 if they are not properly inherited from prior worlds.

**P3-2: Coverage gap for `Finset.not_mem_empty`**
Not used in this world, but could be useful in the next world (union/intersection). Consider mentioning it in L07's prose or conclusion.

## 12. What to Playtest After Patching

After applying P0 and P1 fixes:

1. **L01-L03 with `norm_num` disabled**: Verify that no other single-tactic exploit remains (check `tauto`, `exact?` suggestions).
2. **L08 with `fin_cases` disabled and `simp` disabled**: Verify that the `rw [...] at h` + `rcases` path is the only reasonable approach.
3. **L09 boss with `fin_cases` disabled**: Verify all three parts still require the intended techniques. Check that Part B cannot be solved by `simp at hx ⊢; omega` alone (if `simp` remains enabled on L09).
4. **L05 if title/intro is updated**: Verify the new description matches the task.
5. **Full world re-build**: Verify no regressions after DisabledTactic changes.
