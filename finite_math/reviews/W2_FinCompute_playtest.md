# W2 FinCompute -- Playtest Audit

**World**: W2 FinCompute (8 levels)
**Role**: Lecture world -- introduces `fin_cases`, `decide`, `norm_num`, modular arithmetic, function verification, exhaustive proof
**Prerequisite**: W1 FinIntro (13 levels)
**Auditor posture**: Adversarial. "Compiles" is not a verdict.

---

## 1. Overall Verdict

**NEEDS REVISION** -- the world compiles and has reasonable pedagogical sequencing, but suffers from multiple blocking and high-severity defects: massive statement exploitability (every level is solvable by `decide`), missing tactic documentation for all three newly introduced tactics, no `Branch` alternatives, thin hint design, and granularity issues (L07 plan/implementation mismatch, boss is trivially similar to earlier levels). The world is closer to a clean first draft than a shippable product.

---

## 2. Rubric Scores

| Category | Score | Notes |
|----------|-------|-------|
| 1. Coverage closure | 2 | Core items introduced but not practiced to retrieval/transfer. Modular arithmetic (M4) gets one level. No transfer level. |
| 2. Granularity fit | 2 | L01 and L02 are nearly identical; L04 duplicates L01/L03; L07 plan mismatch. |
| 3. Proof-move teaching | 2 | Only one proof shape taught (exhaustion). The "when to use which" decision is discussed in text but never tested. |
| 4. Inventory design | 1 | Three new tactics introduced with **zero** TacticDoc entries. This is a red-flag violation. |
| 5. Hint design & recoverability | 1 | Minimal hints, no layered hints, no Branch alternatives, no rescue for common wrong moves. |
| 6. Worked example -> practice -> transfer -> boss | 2 | Introduction exists, minimal practice, no transfer. Boss is structurally identical to L07. |
| 7. Mathematical authenticity | 3 | Modular arithmetic connection is nice. Transfer moments exist in conclusions. |
| 8. Paper-proof transfer | 3 | Conclusions consistently translate to paper proof language. |
| 9. Technical fit & maintainability | 2 | Compiles cleanly, but no DisabledTactic/DisabledTheorem, no doc entries, exploitable statements. |

**Average: 2.0** -- below the 3.0 threshold for "good."
**Categories below 2: inventory design (1), hint design (1)** -- both are automatic red flags.

---

## 3. Technical Sanity

### 3a. Build/import issues

None. The project builds successfully (8114 jobs, no errors). Imports are correct.

### 3b. Statement Exploitability -- **P0 (BLOCKING)**

**Every single level in this world is exploitable by `decide`.**

| Level | Intended tactic | Exploitable by | Severity |
|-------|----------------|----------------|----------|
| L01 | `fin_cases i <;> omega` | `intro i; decide` | P0 |
| L02 | `fin_cases i <;> omega` | `intro i; decide` | P0 |
| L03 | `decide` | (intentional -- this is the `decide` intro level) | OK |
| L04 | `fin_cases i <;> omega` | `intro i; decide` | P0 |
| L05 | `norm_num` | `decide` | P0 |
| L06 | `decide` | (intentional) | OK |
| L07 | `fin_cases i <;> omega` | `intro i; decide` | P0 |
| L08 (Boss) | `fin_cases i <;> norm_num` | `intro i; decide` | P0 |

Analysis: `decide` is introduced in L03 and never disabled afterward. Since every subsequent level's goal is a decidable proposition about a small concrete `Fin n`, the learner can solve every remaining level with `intro i; decide` without engaging with `fin_cases`, `norm_num`, or the intended proof patterns. The boss in particular is supposed to integrate `fin_cases` + `norm_num` + `omega`, but `decide` closes it in one tactic.

**The learner can complete the entire world using only `decide` after L03, learning nothing about `fin_cases` or `norm_num`.**

Fix: `decide` must be disabled (`DisabledTactic decide`) in L01, L02, L04, L05, L07, and L08. This is the single most important defect in the world.

Additionally, `omega` can close L05 (`(2 : Fin 7).val * (3 : Fin 7).val = 6`) because after `simp` or definitional unfolding the goal is `2 * 3 = 6` which `omega` handles. This is less severe (the learner at least has to know to try `omega`), but `norm_num` should be the forced path for L05. Consider disabling `omega` in L05 or choosing a statement that `omega` cannot handle (e.g., involving `^` or division).

### 3c. Missing documentation -- **P0 (BLOCKING)**

Three new tactics are introduced with `NewTactic` but have **no `TacticDoc`** entries anywhere in the codebase:

1. `fin_cases` (L01) -- no TacticDoc
2. `decide` (L03) -- no TacticDoc
3. `norm_num` (L05) -- no TacticDoc

This means the player sees these tactics in their inventory but has no documentation panel to reference. This is an automatic red flag per the quality rubric ("missing docs for newly unlocked high-value inventory items").

Fix: Add `TacticDoc` entries for all three tactics in the levels where they are introduced. Each should include:
- What the tactic does
- Minimal example of usage
- When to use it (and when not to)

### 3d. Interactive proof quality

Most levels have good interactive quality -- each step produces visible goal state changes. However:

- **L01**: The proof is `intro i; fin_cases i <;> omega` -- after `fin_cases i`, the semicolon combinator applies `omega` to all goals at once. The learner sees the goal split into 3 goals and then all close simultaneously. This is acceptable but the learner might not understand what `<;>` does. The introduction explains it, which is good.

- **L08 (Boss)**: Same pattern as L01/L02/L07. `fin_cases i <;> norm_num` is a one-shot. The "boss" proof is structurally identical to every other level in the world: `intro i; fin_cases i <;> closer`. No multi-step planning is needed. See Boss Integrity below.

### 3e. No Branch alternatives

No level in the world uses `Branch` to handle alternative proof approaches. This is a problem because:
- L04 explicitly tells the learner to "try both approaches" (`decide` vs `fin_cases`), but there is no Branch to validate the `decide` path
- L05 could be solved by `omega` (see exploitability), but there is no Branch for it
- L06 could potentially be solved by `norm_num` as well as `decide`

Fix: Add `Branch` for all levels where alternative correct approaches exist.

---

## 4. Coverage Sanity

### 4a. Core items coverage

| Item | Plan ID | State in W2 | Assessment |
|------|---------|-------------|------------|
| `fin_cases` | L4 | I (L01), S (L02, L04, L07), G (L08) | Adequate introduction, but S levels are clones of I |
| `decide` | L3 | I (L03), S (L04, L06) | OK |
| `norm_num` | L6 | I (L05), G (L08) | Missing supported practice. Goes directly from I to G. |
| Modular arithmetic (M4) | M4 | I (L06) | **Only one level. No supported practice, no retrieval.** |
| Function on Fin (V19) | V19 | I (L07) | Plan says "define a function by cases" but implementation just proves a property. Mismatch. |
| Tactic selection (V2 meta) | -- | I (L04) | Discussed in text but never tested in a level that forces a choice. |

### 4b. Coverage gaps

1. **`norm_num` has no supported practice level.** It appears in L05 (introduction) and L08 (boss integration). The learner goes from "here is norm_num, try it" directly to "use it in the boss." There should be at least one intermediate level where `norm_num` is used on a slightly harder computation.

2. **Modular arithmetic (M4) gets exactly one level (L06).** This is a surface-only introduction. The learner sees one addition example and never revisits modular arithmetic again. No subtraction example, no multiplication example, no "gotcha" moment where modular behavior surprises. Per the plan, M4 is "supporting" importance, but even supporting items need at least supported practice.

3. **No transfer level.** The plan specifies a transfer moment for W2, but the world has none. Transfer text appears in conclusions (good), but there is no level where the learner is asked to state or demonstrate understanding in a different form.

4. **V19 (recursive/inductive construction on Fin) -- plan mismatch.** The plan says L07 should be "Building a function on Fin n: Define a function Fin 3 -> Nat by cases." The actual L07 is "Verifying a function on Fin" -- it proves a property of a given function, it does not construct a function. The construction move (V19) is not taught.

### 4c. Proof-move coverage

Only one proof move is taught: exhaustive case analysis. The "when to use which" meta-skill (L04) is presented as text but never tested -- the learner is never placed in a situation where `decide` fails and `fin_cases` is needed, or vice versa.

### 4d. Example coverage

The world uses concrete `Fin` types (`Fin 3`, `Fin 4`, `Fin 5`, `Fin 7`) throughout, which is appropriate. However, all examples are structurally identical: "prove an arithmetic property of all elements of Fin n." There is no variety in the type of statement (all are universal quantifiers over Fin n with arithmetic predicates).

---

## 5. Granularity Sanity

### 5a. Levels that are overfine / clones

**L01 and L02 are near-clones.** Both ask: "prove `forall i : Fin n, [arithmetic]`" using `fin_cases i <;> omega`. The only difference is `Fin 3` vs `Fin 4` and the specific arithmetic expression. L02's "dominant lesson" is supposed to be "combining fin_cases + omega," but L01 already does exactly that. The conclusion of L02 adds the comparison with W1's `i.isLt` approach, which is valuable text, but the proof experience is identical to L01.

Fix: Either merge L01 and L02, or make L02 genuinely harder -- e.g., a case where `omega` alone fails and the learner needs to apply a lemma or rewrite in at least one case before `omega`.

**L04 and L01 overlap heavily.** L04 claims to teach "when to use `decide` vs `fin_cases`," but its statement (`forall i : Fin 3, i.val = 0 or i.val >= 1`) is solvable by either tactic interchangeably. The learner does not experience a meaningful difference. There is no level where `decide` fails and `fin_cases` succeeds, or where `fin_cases` is clumsier and `decide` is cleaner.

Fix: Create a contrast pair. One level should have a statement where `decide` fails or times out (e.g., involving a quantifier over a larger type or a non-decidable predicate), forcing `fin_cases`. Another should have a statement where `fin_cases` produces tedious cases but `decide` is instant (already present as L06). This would make the "tactic selection" lesson real rather than theoretical.

**L07 is similar to L01/L02.** Statement: `forall i : Fin 3, 2 * i.val + 1 < 10`. Proof: `intro i; fin_cases i <;> omega`. The "function verification" framing is different, but the proof experience is the same exhaustion pattern. The plan intended this level to involve *defining* a function, not just proving a property.

### 5b. Center of gravity

The world's center of gravity is supposed to be "computing with Fin: exhaustive case analysis and computational automation." The actual center is narrower: "using `fin_cases i <;> omega/norm_num` to verify arithmetic." Five of the eight levels (L01, L02, L04, L07, L08) use essentially the same proof pattern.

### 5c. Boss seeding

The boss (L08) requires `fin_cases` + `norm_num`. The `fin_cases` component is heavily seeded (5 prior levels use it). The `norm_num` component is minimally seeded (1 prior level). The `^` operator in the boss is the only place exponentiation appears, but `norm_num` handles it without the learner needing to understand anything new -- so this is not a surprise burden per se, just a weak integration demand.

---

## 6. Learner Simulation

### 6a. Attentive novice

**First stuck point**: L01. After `intro i`, the novice sees the goal `i.val < 10` with `i : Fin 3` in context. The introduction says to use `fin_cases i`, but the novice has never seen this tactic. There is no `TacticDoc` to reference. The hint says "use `fin_cases i <;> omega`" which gives away the full answer. The novice types the answer, it works, but they may not understand *why*.

Improvement needed: The hint should be layered. First hint: "You want to check every possible value of `i`. What tactic splits `i : Fin n` into separate cases?" Second hint (hidden): "Try `fin_cases i`. After splitting, each case is arithmetic that `omega` can handle."

**Most likely wrong move**: After learning `decide` in L03, the novice will try `decide` on every subsequent level, because it is simpler. Since `decide` is never disabled, the novice *succeeds* with this approach and never learns `fin_cases` or `norm_num`. This is the core exploitability problem.

**Rescue quality**: Poor. Hints are one-shot (give the answer immediately), not layered. No common-error hints (e.g., for a novice who tries `simp` or `omega` alone on the boss).

### 6b. Experienced Lean user

**Avoidable friction**: Minimal. The proofs are short and the tactics are standard. An experienced user would find this world trivially easy -- every level is one or two tactics.

**Alias gaps**: Not applicable at this level of complexity.

**Inventory clutter**: No issues. Only three tactics are added, and they are genuinely useful.

**Needless forced verbosity**: None. The proofs are already minimal.

**Biggest complaint**: The experienced user would note that L01, L02, L04, and L07 are essentially the same problem repeated. They would also immediately use `decide` everywhere and wonder why `fin_cases` exists.

---

## 7. Boss Integrity Check

### 7a. Statement

```lean
Statement : forall i : Fin 5, 0 < i.val ^ 2 + 1 and i.val ^ 2 + 1 < 20 := by
```

### 7b. Seeded subskills

| Subskill | Where seeded | Assessment |
|----------|-------------|------------|
| `intro` | W1 baseline | OK |
| `fin_cases` | L01, L02, L04, L07 | Over-seeded (4 identical uses) |
| `norm_num` | L05 | **Under-seeded (1 use)** |
| `omega` | W1, L01, L02, L04, L07 | OK (not needed in boss) |
| Conjunction (`and`) | Not taught in W2 | **New burden in boss** |
| Exponentiation (`^`) | Not used before | **New notation in boss** |

### 7c. Surprise burdens

1. **Conjunction**: The boss goal has `and`, which requires `constructor` or the learner needs to know that `norm_num` handles conjunctions. The `and` is never discussed or practiced in W2. This is a hidden prerequisite. However, `constructor` was taught in W1 and `fin_cases i <;> norm_num` handles the conjunction automatically, so the surprise is mitigated IF the learner uses the semicolon combinator.

2. **Exponentiation (`^`)**: Appears for the first time. The introduction explains that `norm_num` handles it, so this is not a stuck point, but it is a new notation that could confuse a novice.

### 7d. Integration quality -- **GAUNTLET BOSS**

The boss proof is `intro i; fin_cases i <;> norm_num`. This is structurally identical to every other level in the world. The only difference is that `norm_num` replaces `omega` as the closer (because `^` is involved).

This is a **gauntlet boss** per the failure taxonomy: it does not require the learner to plan, combine moves in a novel way, or see the whole structure. The learner replays the same `fin_cases <;> closer` pattern from L01/L02/L07 with a different closer. There is no integration challenge -- just substitution.

Fix: The boss should require a multi-step proof where the learner must choose between tactics, apply a lemma, or combine `fin_cases` with manual reasoning in at least one case. For example:
- A goal where some cases need `omega` and some need `norm_num` (forcing the learner to handle cases individually rather than with `<;>`)
- A goal that requires using a result from W1 (e.g., `Fin.isLt`, `congr_arg`) alongside `fin_cases`
- A goal where the learner must construct a function (V19 per the plan) and then verify it

### 7e. Could the learner explain why the proof works?

Barely. The learner would say "I checked all five cases and norm_num verified each one." This is correct but trivial -- it is the same explanation they would give for L01. A boss should produce a richer explanation.

---

## 8. Course-Role Sanity

The world is cast as a **lecture** world. Lectures should introduce, provide supported practice, and culminate in a boss that integrates.

Assessment: The world introduces three tactics and one mathematical concept (modular arithmetic). However:
- Introduction is adequate for `fin_cases` and `decide`, thin for `norm_num`
- Supported practice is repetitive (same proof shape) rather than graduated
- Transfer is absent
- The boss does not integrate meaningfully

The world plays its role as an introduction but fails as a lecture that achieves mastery. It is more like a "here are three new buttons" demo than a lesson.

---

## 9. Ranked Patch List

### P0 -- Blocking

| # | Defect | Fix |
|---|--------|-----|
| P0-1 | **Statement exploitability**: Every level after L03 is solvable by `decide`, bypassing the intended lesson | Add `DisabledTactic decide` to L01, L02, L04, L05, L07, L08. Re-enable only in L03 and L06 where it is the intended tactic. |
| P0-2 | **Missing TacticDoc**: `fin_cases`, `decide`, and `norm_num` have no documentation entries | Add `TacticDoc fin_cases`, `TacticDoc decide`, and `TacticDoc norm_num` in L01, L03, and L05 respectively. Each should include purpose, syntax, minimal example, and when-to-use guidance. |

### P1 -- High

| # | Defect | Fix |
|---|--------|-----|
| P1-1 | **Gauntlet boss**: L08 uses the same `fin_cases <;> closer` pattern as L01/L02/L07 with no novel integration | Redesign the boss to require multi-step reasoning. Options: (a) a statement where some cases need manual reasoning (e.g., applying a lemma + omega) while others need norm_num, so `<;>` alone doesn't work; (b) a statement that integrates W1 skills (e.g., prove `Fin.castSucc i != Fin.last 4` for specific i using `fin_cases` to reduce to concrete cases, then value-level reasoning); (c) a two-part boss where one part requires exhaustion and the other requires a different approach. |
| P1-2 | **L07 plan mismatch**: Plan says "build a function Fin 3 -> Nat by cases" (V19 introduction), but implementation just proves a universal property (same as L01/L02) | Rewrite L07 to actually construct a function on `Fin n` by cases. E.g., define a function using `Fin.cases` or a `match` and prove it satisfies a spec. This teaches V19 as planned. |
| P1-3 | **`norm_num` has no supported practice**: Goes from introduction (L05) directly to boss (L08) | Add a supported-practice level for `norm_num` between L05 and the boss. This level should use `norm_num` on a slightly harder computation (e.g., involving `^` or `%`), previewing its use in the boss. |
| P1-4 | **No Branch alternatives**: L04 explicitly tells learners to try both approaches but has no Branch | Add `Branch` for `decide` path in L04. Add `Branch` for `omega` path in L05. Add `Branch` for alternative approaches in L06 and L08 where multiple tactics work. |

### P2 -- Medium

| # | Defect | Fix |
|---|--------|-----|
| P2-1 | **L01/L02 near-clones**: Both are `forall i : Fin n, [arithmetic]` solved by `fin_cases <;> omega` | Either merge (moving the W1-comparison text to L01's conclusion) or make L02 genuinely different -- e.g., a case where one branch of `fin_cases` needs `rw` before `omega`, teaching that `fin_cases` gives you control over individual cases. |
| P2-2 | **L04 does not teach tactic selection**: `decide` and `fin_cases` are interchangeable on the given statement | Replace with a contrast pair: one level where `decide` is clearly better (already exists as L06), one where `fin_cases` is necessary because the per-case reasoning is non-decidable or `decide` times out. |
| P2-3 | **Modular arithmetic (M4) has only one level**: No subtraction, no multiplication, no "gotcha" moment | Add at least one more modular arithmetic level: e.g., subtraction wrapping or a multiplication that surprises the learner. |
| P2-4 | **Hint design is thin**: All hints give the answer immediately, no layered hints, no wrong-move rescue | Rewrite hints throughout the world to be layered: strategy hint first (visible), code template second (hidden). Add hints for common wrong moves (e.g., trying `omega` on a goal with `^`). |
| P2-5 | **Conjunction (`and`) in boss is an untaught micro-burden**: The boss goal has `and` but W2 never uses conjunction | Either add a level before the boss that uses `and` with `fin_cases`, or simplify the boss to avoid conjunction (use two separate statements), or add a hint explaining that `norm_num` handles conjunctions. |
| P2-6 | **`omega` can close L05**: The `norm_num` introduction level can be solved by `omega` | Either disable `omega` in L05, or change the statement to something `omega` cannot handle (e.g., involving `^` or factorial). |

### P3 -- Low

| # | Defect | Fix |
|---|--------|-----|
| P3-1 | **No transfer level**: The plan mentions transfer but the world has none | Consider adding a transfer-style level at the end (or as part of the conclusion), e.g., a level where the learner must state in structured form which approach they would use for a given problem. |
| P3-2 | **Boss conclusion says "Congratulations on completing the Computing with Fin world"**: Should summarize the method and point to reuse contexts more explicitly | Strengthen the conclusion to emphasize when each tactic is useful in future worlds, with a table (already present, which is good). |

---

## 10. What to Playtest Again After Patching

After implementing the patches above, re-audit:

1. **Exploitability**: Verify that `decide` is properly disabled in all levels except L03 and L06. Test that no other one-shot tactic (e.g., `simp`, `aesop`, `native_decide`) bypasses intended proofs.
2. **Boss integrity**: Verify the redesigned boss requires genuine multi-step reasoning and cannot be solved by `<;>` alone.
3. **L07 function construction**: Verify the new L07 actually teaches V19 (defining a function by cases) rather than just proving a property.
4. **Hint quality**: Walk through each level as a novice and check that layered hints rescue without spoiling.
5. **norm_num coverage closure**: Verify the new supported-practice level creates a smooth path from introduction to boss.
6. **TacticDoc completeness**: Verify all three new tactics have documentation panels that appear in the player's inventory.
7. **Branch validation**: Verify all Branch alternatives lead to valid complete proofs.

---

## Summary

The world has a sound pedagogical arc (introduce three computational tactics for Fin, practice them, integrate in boss) but the execution has serious gaps. The exploitability defect (P0-1) alone means the world teaches nothing after L03 -- the learner can `decide` their way to victory without engaging with `fin_cases` or `norm_num`. The missing documentation (P0-2) means newly introduced tactics have no reference panel. The boss is a gauntlet that replays the same pattern as half the world's levels. These must be fixed before the world is shippable.

The world also lacks variety in proof experience (5 of 8 levels use the exact same proof shape), misses the plan's V19 construction objective, and under-covers modular arithmetic and `norm_num`. Fixing these would turn a repetitive tutorial into a genuinely instructive lecture world.
