# W1 SetsAndMembership -- Playtest Audit v1

## 1. Overall Verdict

**FAIL**

There are 5 P0 defects (exploitable levels where the learner can bypass the intended lesson using undisabled library lemmas) and 3 P1 defects. The boss is completely exploitable via `le_antisymm`, which is not disabled. Multiple earlier levels are exploitable by one-shot library lemmas (`subset_refl`, `Set.Subset.trans`, `Set.empty_subset`, `bot_le`, `rfl`). Level 8 (first ext teaching level) is solvable with `rfl` without ever using `ext`.

## 2. Rubric Scores

| Category | Score | Notes |
|---|---|---|
| Coverage closure | 2 | `Set.univ` introduced but never practiced; `∅` gets one level but no retrieval |
| Granularity fit | 3 | Each level has one dominant lesson; L06 is slightly overloaded (two definitions, only one practiced) |
| Proof-move teaching | 3 | The ext-constructor-chase pattern is well taught; specialize is well introduced |
| Inventory design | 2 | `unfold` introduced in the boss (violates "boss integrates, never introduces"); `Set.univ` introduced but never used |
| Hint design / recoverability | 3 | Hints are well-layered and strategic; no rescue for off-path learners on L09 (no hint for `and_comm` path) |
| Worked example -> practice -> boss | 2 | L08 (ext first contact) is trivially solvable by `rfl`, defeating the worked-example purpose; boss is one-shot by `le_antisymm` |
| Mathematical authenticity | 3 | Good explanation of sets-as-predicates; conclusion on L11 connects to paper proof |
| Paper-proof transfer | 3 | L11 conclusion does an excellent natural-language translation |
| Technical fit / maintainability | 2 | Multiple undisabled library lemmas create exploit paths on 7 of 11 levels |

**Average: 2.6 -- Below the 3.0 threshold. Two categories below 2.**

## 3. Coverage Gaps

### 3a. `Set.univ` introduced but never practiced
- L06 introduces both `∅` and `Set.univ` with `NewDefinition` and doc entries.
- The level statement is `∅ ⊆ A`. There is no level proving anything involving `Set.univ`.
- `Set.univ` appears only in prose text and the conclusion's "key facts" list.
- Coverage state: **I only** (introduced, never practiced, never retrieved, never integrated).

### 3b. No retrieval level for `show`/`change`
- `show` is introduced in L01, `change` in L02. Neither is required again until possibly the boss.
- The boss proof does not use `show` or `change`. So these tactics are introduced, practiced once each, and then abandoned for the rest of the world.
- Coverage state: **I only** for both.

### 3c. `hx.elim` / `False.elim` -- no retrieval
- L06 introduces `hx.elim` for eliminating `False` hypotheses. This proof move never recurs.
- The boss does not require it. No later level retrieves it.

### 3d. `.mp`/`.mpr` -- introduced in conclusion only
- L07's conclusion mentions `h.mp` and `h.mpr` for using iff hypotheses. These are never required in any level statement. The boss could use them (L11 has subset hypotheses, not iff hypotheses), but doesn't.
- L10 uses `(h x).mp hx` and `(h x).mpr hx` in its proof, which is first contact for `.mp`/`.mpr` usage, but L07 introduced them only in text.

## 4. Granularity Defects

### 4a. L06: Two definitions, one practiced
- L06 title is "The Empty Set and the Universal Set" but only proves `∅ ⊆ A`.
- `Set.univ` gets definition and documentation but no practice.
- **Fix**: Either split into two levels (L06a: empty set; L06b: universal set), or add `A ⊆ Set.univ` as a second statement, or remove `Set.univ` from this level and introduce it when it's actually needed.

### 4b. L08: Trivially solvable -- first-contact level defeats its own purpose
- L08 is the first-contact level for `ext`. Statement: `{x | P x} = {x | P x}`.
- This is solvable by `rfl` (both sides are syntactically identical).
- The level exists to teach `ext -> constructor -> chase`, but a learner who types `rfl` learns nothing about extensionality.
- **Fix**: Make the two sets syntactically different but definitionally equal, e.g., `{x | P x} = {x | P x ∧ True}` or use a different formulation that can't be solved by `rfl`.

### 4c. L11 Boss: New tactic `unfold` introduced
- The boss level has `NewTactic unfold` and a `TacticDoc unfold`.
- `unfold` is not used in the boss proof. It is not mentioned in any hint.
- Introducing a new tactic in the boss violates "boss integrates, never introduces."
- **Fix**: Move `unfold` introduction to an earlier level where it's actually practiced, or remove it from this world entirely.

## 5. Statement Exploitability (P0 Defects)

### P0-1: L03 (Subset Reflexivity) -- one-shot by `subset_refl` / `le_refl`
- **Statement**: `A ⊆ A`
- **Intended lesson**: Introduce the `intro x; intro hx` pattern for subset proofs.
- **Exploits**: `exact subset_refl A`, `exact le_refl A`, `exact Set.Subset.refl A`, `exact fun _ a => a`
- All bypass the intro lesson entirely.
- **Fix**: `DisabledTheorem subset_refl Set.Subset.refl le_refl` on this level. The `fun` term-mode proof is harder to block but is less likely for a novice.

### P0-2: L05 (Subset Transitivity) -- one-shot by `Set.Subset.trans` / `h1.trans h2`
- **Statement**: `A ⊆ B -> B ⊆ C -> A ⊆ C`
- **Intended lesson**: Chain two subset hypotheses using `have` intermediate.
- **Exploits**: `exact Set.Subset.trans h1 h2`, `exact h1.trans h2`, `exact le_trans h1 h2`
- **Fix**: `DisabledTheorem Set.Subset.trans le_trans` on this level.

### P0-3: L06 (Empty Set) -- one-shot by `Set.empty_subset` / `bot_le`
- **Statement**: `∅ ⊆ A`
- **Intended lesson**: Empty set membership is `False`; use `hx.elim` for vacuous truth.
- **Exploits**: `exact Set.empty_subset A`, `exact bot_le`
- **Fix**: `DisabledTheorem Set.empty_subset bot_le` on this level.

### P0-4: L08 (Set Extensionality first contact) -- one-shot by `rfl`
- **Statement**: `{x | P x} = {x | P x}`
- **Intended lesson**: First contact with `ext` tactic.
- **Exploit**: `rfl` -- both sides are syntactically identical.
- **Fix**: Change the statement so the two sides are syntactically different. For example: `{x : N | P x ∧ True} = {x : N | P x}` or `{x : N | True ∧ P x} = {x : N | P x}`, which requires `ext` + `constructor` + propositional reasoning.

### P0-5: L11 Boss -- one-shot by `le_antisymm` / `h1.antisymm h2` / `Subset.antisymm`
- **Statement**: `A ⊆ B -> B ⊆ A -> A = B`
- **Intended lesson**: Integrate ext + constructor + subset application.
- **Disabled**: Only `Set.Subset.antisymm`.
- **Exploits**: `exact le_antisymm h1 h2`, `exact h1.antisymm h2`, `exact Subset.antisymm h1 h2`, `exact Set.eq_of_subset_of_subset h1 h2`, `exact LE.le.antisymm h1 h2`
- The boss is completely exploitable. Only one of many names for the antisymmetry theorem is disabled.
- **Fix**: `DisabledTheorem le_antisymm Subset.antisymm Set.eq_of_subset_of_subset LE.le.antisymm` in addition to the existing `Set.Subset.antisymm` disable.

## 6. Additional Exploit Analysis (P1)

### P1-1: L07 (If and Only If) -- one-shot by anonymous constructor `⟨hpq, hqp⟩`
- **Statement**: `P -> Q -> Q -> P -> P <-> Q` (with named hypotheses)
- **Exploit**: `exact ⟨hpq, hqp⟩` or `exact Iff.intro hpq hqp`
- This bypasses `constructor`. However, anonymous constructors are NNG4 knowledge, and the level's conclusion mentions this as a possibility. The learner still sees the iff structure.
- **Severity**: P1. The anonymous constructor still requires the learner to understand iff has two components. But the `constructor` lesson is skipped.
- **Fix**: Consider restructuring so at least one direction requires work (e.g., `(P /\ R -> Q) -> (Q -> P) -> (Q -> R) -> P <-> Q`). Or accept this as an intentional alternative path.

### P1-2: L09 (Ext with Work) -- `ext x; exact and_comm` bypasses obtain/constructor
- **Statement**: `{x | P x /\ Q x} = {x | Q x /\ P x}`
- **Exploit**: After `ext x`, `exact and_comm` closes the iff goal in one step, bypassing `constructor`, `obtain`, and the conjunction manipulation lesson.
- **Fix**: `DisabledTheorem and_comm And.comm` on this level. Or change the statement to something that isn't a direct application of `and_comm` (e.g., `{x | P x /\ Q x /\ R x} = {x | Q x /\ R x /\ P x}` which requires more than one rewrite).

### P1-3: L10 (Double Inclusion) -- `ext x; exact h x` bypasses Set.Subset.antisymm lesson
- **Statement**: `{x | P x} = {x | Q x}` given `forall x, P x <-> Q x`
- **Intended lesson**: Teach `Set.Subset.antisymm` (double inclusion).
- **Exploit**: `ext x; exact h x` completely avoids the double-inclusion approach and uses ext instead.
- This is a significant pedagogical problem: the level meant to teach double inclusion can be solved more easily with ext (which was just learned).
- **Fix**: Either disable `ext` for this level (forcing double inclusion) or redesign the statement so `ext` doesn't produce a trivially closable iff. For example, give two concrete set-builder sets whose equivalence requires using a hypothesis, where the hypothesis is naturally phrased as subset relationships rather than pointwise iff.

## 7. Learner Simulation

### Attentive Novice (NNG4-complete)

**L01**: Learner reads intro, sees `show 5 > 3`, types it successfully. Then types `omega`. Clean experience. **First stuck point**: None -- well guided. The novice will not think of `rfl` because the goal doesn't look like `_ = _`.

**L02**: Learner follows hints for `change x > 5 at hx`, then `change x > 3`. This works. **Risk**: The learner might try `omega` first (from NNG4 habit), which fails silently with set membership goals. No hint covers this stuck state. The learner has no feedback explaining WHY omega failed.

**L03**: Learner follows `intro x`, `intro hx`, `exact hx`. **Risk**: An NNG4-experienced learner may type `assumption` instead of `exact hx` (which works). Not a problem -- `assumption` is known from NNG4. **Exploit risk**: A learner who remembers seeing `subset_refl` in a textbook or documentation could type `exact subset_refl A`. No hint warns against this.

**L04**: Well designed. `specialize h hx` is clear. The alternative `exact h hx` is mentioned in the conclusion. Clean experience.

**L05**: `have hxB : x ∈ B := h1 hx` is the intended proof. **Stuck point**: The `have` syntax with type annotation and `:=` is a potential friction point. The NNG4 learner knows `have` but may not remember the `:= proof` syntax (vs `have ... by ...`). The hint gives the full syntax, which helps. **Exploit risk**: `exact h2 (h1 hx)` is mentioned in the conclusion and is an acceptable shortcut.

**L06**: After `intro x hx`, the learner sees `hx : x ∈ ∅`. **Stuck point**: The learner needs to realize this is `False`. The hint explains this well. `exact hx.elim` is new syntax -- `.elim` on a `False` proof. This is the first time the learner sees dot notation used this way. No previous level teaches this pattern. **Risk**: Moderate -- the hint is clear, but this is a new micro-skill (dot notation for eliminator) introduced without prior setup. An alternative `contradiction` (NNG4 tactic) also works and is more natural. The hint should mention `contradiction` as an alternative.

**L07**: Clean experience. `constructor` splits iff, each direction is trivially `exact hpq` / `exact hqp`.

**L08**: **Critical problem**. The statement `{x | P x} = {x | P x}` is solvable by `rfl`. A learner who tries `rfl` first (a natural instinct for `_ = _` goals from NNG4) will solve the level without ever learning `ext`. The ext lesson is the most important lesson in the world. This level must not be solvable by `rfl`.

**L09**: After mastering ext from L08 (assuming L08 is fixed), the learner does `ext x`, `constructor`, then needs to manipulate conjunctions. `obtain ⟨hp, hq⟩ := h` and `exact ⟨hq, hp⟩` use angle-bracket syntax from NNG4. Clean experience IF the learner doesn't discover `and_comm`.

**L10**: The learner is supposed to learn `Set.Subset.antisymm` here. But they just learned `ext` two levels ago and may naturally try `ext x; exact h x` instead, which works and completely bypasses the intended lesson. The level needs restructuring.

**L11 (Boss)**: The boss is well-designed IF the exploit paths are closed. With `le_antisymm` available, a learner who consults the inventory or tries `exact le_antisymm h1 h2` solves the boss in one step.

### Experienced Lean User

**Friction points**:
- L01-L02: An experienced user knows `omega` should work on arithmetic-in-disguise but it fails without `show`/`change`. This is actually good pedagogy (forces learning about definitional equality) but may cause brief confusion.
- L08: `rfl` is the obvious solution for an experienced user. The level fails its purpose.
- L11: `le_antisymm` is the first thing an experienced user tries. The boss is trivially broken.

**Missing aliases**: None observed -- the proof paths are clean.

**Inventory clutter**: `unfold` appearing in the boss's NewTactic list is confusing -- the boss doesn't use it and it wasn't taught before.

## 8. Boss Integrity

### Seeded subskills
- `ext`: Introduced L08, practiced L09. **OK** (2 prior uses).
- `constructor` (for iff): Introduced L07, used in L08, L09. **OK** (3 prior uses).
- `intro` for subset: Introduced L03, used L04, L05, L06. **OK** (4 prior uses).
- Subset hypothesis application: Introduced L04, used L05. **OK** (2 prior uses).

### Closure quality
- **Adequate** for the core skills. Each boss subskill has at least introduction + practice.

### Integration quality
- The boss requires `ext` + `constructor` + two subset applications in the two iff directions. This is a genuine integration of the world's three main moves. **Good** if exploits are closed.

### Surprise burden
- `unfold` is introduced as `NewTactic` in the boss. This is a surprise burden. It should be moved earlier or removed.
- Otherwise no surprise burden -- all moves are pre-taught.

### Can the learner explain the proof?
- Yes. The conclusion does an excellent job translating the proof to natural language. This is one of the world's strengths.

## 9. Technical Risks

### 9a. `omega` import dependency
- `omega` is used in L01 and L02 but not explicitly imported. It comes through `Mathlib.Data.Set.Basic`. If the import chain changes, these levels break. Low risk but worth noting.

### 9b. Hint misfiring on L06
- L06 hint says to use `exact hx.elim`. But after `intro x hx`, if the learner types `exfalso` first (which changes the goal to `False`), then `exact hx` works. There is no hint for this alternative path.

### 9c. `Set.Mem` definitional unfolding
- The game relies on `x ∈ {y | P y}` being definitionally equal to `P x`. This works in current Lean 4 but is a core language behavior. If Lean changes definitional equality rules, many levels break.

## 10. Ranked Patch List

### P0 (Blocking -- must fix before shipping)

1. **P0-1**: L11 Boss: Disable `le_antisymm`, `Subset.antisymm`, `Set.eq_of_subset_of_subset`, `LE.le.antisymm` in addition to `Set.Subset.antisymm`.
2. **P0-2**: L08: Change statement from `{x | P x} = {x | P x}` to something where both sides are syntactically different (e.g., `{x | P x ∧ True} = {x | P x}`), making `rfl` fail.
3. **P0-3**: L03: Disable `subset_refl`, `Set.Subset.refl`, `le_refl` for this level.
4. **P0-4**: L05: Disable `Set.Subset.trans`, `le_trans` for this level.
5. **P0-5**: L06: Disable `Set.empty_subset`, `bot_le` for this level.

### P1 (High -- should fix before shipping)

6. **P1-1**: L09: Disable `and_comm`, `And.comm` for this level, OR change the statement so `and_comm` alone doesn't close the iff.
7. **P1-2**: L10: Disable `ext` for this level (forcing double inclusion), OR redesign the statement so ext doesn't trivially bypass the lesson.
8. **P1-3**: L11 Boss: Move `NewTactic unfold` out of the boss. Either introduce it in an earlier level (with practice) or remove it from W1 entirely.

### P2 (Medium -- improve if possible)

9. **P2-1**: L06: Add a second level or part for `Set.univ`. Currently `Set.univ` is introduced but never practiced.
10. **P2-2**: L02: Add a hint for the stuck state where the learner tries `omega` first and it fails. Explain that `omega` can't see through set membership notation.
11. **P2-3**: L06: Add `contradiction` as an alternative path in the hints (NNG4-known tactic that also works).
12. **P2-4**: Add a retrieval level for `show`/`change` later in the world. These tactics are introduced early but never used again.

### P3 (Low -- nice to have)

13. **P3-1**: L07: Consider restructuring so `⟨hpq, hqp⟩` doesn't one-shot the level (but this is debatable since anonymous constructors are NNG4 knowledge).
14. **P3-2**: L05: The `have hxB : x ∈ B := h1 hx` syntax in the hint is a lot to type correctly. Consider showing `have hxB := h1 hx` (type-inferred) as the primary hint.

## 11. What to Playtest Again After Patching

1. **L08 (redesigned statement)**: Verify the new statement teaches `ext` and isn't solvable by trivial alternatives.
2. **L11 Boss (with all antisymm aliases disabled)**: Verify no remaining one-shot paths. Check that the intended proof still works.
3. **L03, L05, L06 (with disabled theorems)**: Verify the intended proofs still work and the `DisabledTheorem` list is complete.
4. **L09 (with `and_comm` disabled)**: Verify the intended proof still works.
5. **L10 (redesigned or ext-disabled)**: Verify the double-inclusion lesson is actually forced.
6. **New `Set.univ` level (if added)**: Verify it teaches something meaningful.
7. **`unfold` (wherever it's moved)**: Verify it has a practice level before the boss, or is removed.
