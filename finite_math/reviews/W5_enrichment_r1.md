# W5 FinsetConstructors -- Enrichment Review (Round 1)

## Ranked suggestions

### 1. L02 never introduces `Finset.singleton` as a definition

**What**: L02 is titled "Singletons" and the plan says its coverage item is "Construct `{5}` as `Finset.singleton 5`" (M6 (S)), but the level never names `Finset.singleton`, has no `NewDefinition Finset.singleton`, and has no `DefinitionDoc` for it. The introduction says `{5}` is `insert 5 empty` under the hood, but the level skips the intermediate concept `Finset.singleton` entirely.

**Why**: `Finset.singleton` is a genuine API surface in mathlib. Learners will encounter it in goal states and lemma names (e.g., `Finset.mem_singleton`, `Finset.card_singleton`). The plan explicitly asks for it. Omitting the definition here creates a gap: the learner goes from `empty` directly to `insert` without ever seeing that the singleton has its own constructor. Later in W6 (L03), `mem_singleton` appears -- the learner will wonder what `singleton` is.

**Where**: L02. Add a `DefinitionDoc Finset.singleton` and `NewDefinition Finset.singleton`. Optionally change the statement to something that makes `Finset.singleton` visible, e.g., prove `Finset.singleton 5 = {5}` (which is `rfl`) as a first sub-goal, then prove its cardinality is 1 as a second. This would also give L02 a non-`decide` proof step, which is pedagogically better (see suggestion #3).

**Effort**: Medium (modify level statement + add definition doc)

**Recommend**: Yes

---

### 2. L02 relies on `decide` for the proof, but `decide` is not formally in the learner's inventory for this world

**What**: L02's proof is `decide`, L06's proof is `decide`, L07 uses `decide` after `use 1`, and L08 uses `decide` for the cardinality sub-goal. But `decide` was introduced in W2 (FinCompute L03), and L02 does not have `NewTactic decide` or any note about why `decide` is available here. Meanwhile, L01, L03, L04, L05 all disable `decide`. The inconsistency is confusing: `decide` is disabled in some levels but quietly enabled and required in others, with no explanation of why.

**Why**: The learner experiences a jarring pattern: L01 uses `rfl`, L02 suddenly uses `decide`, L03 goes back to `rfl` with `decide` disabled, L04 uses `rfl` with `decide` disabled, L05 uses `rw` with `decide` disabled, L06 uses `decide` again, L07 uses `use` + `decide`, L08 uses `decide` for part 3. The world never explains why `decide` appears and disappears. This is a pedagogical hazard: the learner cannot predict which tool is available.

**Where**: All levels. The world needs a consistent policy. Two options:
- (A) Enable `decide` in all levels and explain at the start that concrete computations on finsets are decidable. Then the `rfl` levels teach "this is definitional" while `decide` levels teach "this requires computation."
- (B) Disable `decide` in all levels and use `rfl`/`rw`/`norm_num` everywhere, adding a note that `decide` could also handle these goals.

Option (A) is more honest and better sets up W6 where `decide` will be a regular tool.

**Effort**: Medium (audit and unify DisabledTactic lines across all 8 levels, add a sentence to L01 or L02 intro about `decide` availability)

**Recommend**: Yes

---

### 3. L02 and L06 are pure `decide` levels with no proof moves to practice

**What**: L02's entire proof is `decide`. L06's entire proof is `decide`. The learner types one tactic and moves on. These levels have zero proof-move content -- they are "press the button" levels.

**Why**: The plan says L02 should cover "Construct `{5}` as `Finset.singleton 5`" and L06 should cover "C2 misconception: DecidableEq." Both deserve richer proof goals. For L02: proving `Finset.singleton 5 = {5}` (rfl) AND `{5}.card = 1` (decide) would give two steps and expose `Finset.singleton`. For L06: the plan says the learner should "encounter a type-class error." But the current level never shows a type-class error -- it just has the learner prove a cardinality fact about a custom type. The introduction *talks about* what would go wrong without `DecidableEq`, but the learner never *sees* it fail. This is telling vs. showing.

**Where**: L02, L06.

For L06 specifically: consider structuring it as two parts. Part 1: attempt to insert into a type without `DecidableEq` (which would produce a type error -- perhaps shown as a sorry'd example in the introduction with the actual error message). Part 2: the same operation on a type with `DecidableEq` (the current goal). The "before and after" structure is much more powerful for misconception correction than describing the error in prose.

**Effort**: Medium (L02), Medium (L06)

**Recommend**: Yes (L06 especially -- misconception levels that only tell and never show are underperforming)

---

### 4. L07 (Finset vs Set) diverges from the plan: it should show a failed Set lemma, but instead proves Nonempty

**What**: The plan says L07 should "Attempt to apply a `Set` lemma to a `Finset` and see why it fails" (coverage items C1 (W), M35 (preview)). The actual level proves `Finset.Nonempty {1,2,3}`, which is useful but is not the planned misconception level. The introduction discusses Finset vs Set conceptually, and the conclusion mentions the API incompatibility, but the *proof goal* has nothing to do with Set at all.

**Why**: The C1 misconception ("Finset is not Set") is one of the most important conceptual distinctions in this course. Having a level where the learner tries to apply `Set.mem_union` to a `Finset` (and sees the type error), then uses the correct `Finset.mem_union` (or a simpler Finset lemma) would be far more impactful than the current Nonempty goal. The Nonempty goal could live anywhere -- it doesn't specifically teach Finset-vs-Set.

**Where**: L07. Replace or augment the current goal with one that actually involves a Set/Finset confusion. For example: given `s : Finset Nat`, prove something using a `Finset`-specific lemma, with a hint that says "you might be tempted to use `Set.mem_insert`, but that's for `Set`, not `Finset` -- use `Finset.mem_insert` instead." The `Finset.Nonempty` goal could be kept as a warm-up sub-goal.

**Effort**: High (restructure the level)

**Recommend**: Yes

---

### 5. The world has no `Finset.singleton_eq_insert_empty` derivation

**What**: The relationship `{a} = insert a empty` is mentioned in prose (L02 intro: "Under the hood, `{5}` is the same as `insert 5 empty`") but never proved as a goal. This is a derivable result presented as a fact.

**Why**: Proving `(Finset.singleton 5 : Finset Nat) = insert 5 empty` (which is `rfl`) would connect L01 (empty) and L02 (singleton) to L03 (insert). It shows that the three constructors form a coherent system where singleton is derivable from the other two. This is the kind of structural insight that deepens understanding. It also gives the learner a concrete example of how `insert` builds on `empty` before L03 introduces `insert` for multi-element finsets.

**Where**: L02 or as a new sub-goal within L02. If L02 is modified per suggestion #1, this could be the first of two sub-goals: (1) `Finset.singleton 5 = insert 5 empty` by `rfl`, (2) `{5}.card = 1` by `decide`.

**Effort**: Low (add as a sub-goal)

**Recommend**: Yes

---

### 6. No level explores what happens when you insert a duplicate

**What**: The introduction in L03 says "If `a` is already in `s`, then `insert a s = s` -- inserting a duplicate has no effect. (You will see this idempotency property in a later world.)" But this is a conceptual preview with no proof. The boss (L08) also doesn't test this.

**Why**: Insert idempotency is coverage item C7, which is addressed in W6 L06. The plan explicitly places it there, so this is not a gap in W5 per se. However, the world constructs finsets for 8 levels without the learner ever experiencing what happens with a duplicate. The world promises the learner "can construct finsets ... and understands" the tools, but insert's most distinctive behavior (silently dropping duplicates) is never witnessed. Even a single sub-goal in L03 or L04 -- e.g., prove `insert 1 {1, 2} = {1, 2}` -- would ground the prose claim.

**Where**: L03 or L04 (add a sub-goal).

**Effort**: Low (add a conjunction sub-goal)

**Recommend**: Consider (the plan places this in W6, so it's acceptable to defer, but showing it once here would strengthen the world)

---

### 7. The boss level (L08) doesn't test `DecidableEq` or `Finset vs Set`

**What**: L08 integrates L01-L05 skills (rfl for notation, `cons_eq_insert`, `decide` for cardinality) but completely ignores L06 (DecidableEq) and L07 (Finset vs Set). Two of the world's eight levels are not represented in the boss.

**Why**: The boss should integrate the world. L06 and L07 are conceptual levels with distinct coverage items (M15, C2, C1, M35). If the boss doesn't touch them, they feel like detached asides. Adding a sub-goal that uses a non-Nat type (testing DecidableEq) or a goal that involves `Finset.Nonempty` (connecting L07) would unify the world.

**Where**: L08. Add a fourth conjunct, e.g., proving `({Color.red, Color.green} : Finset Color).card = 2` (requires `DecidableEq` on `Color`, reusing the type from L06). Or prove `(insert Color.red {Color.blue} : Finset Color).Nonempty` (connecting L07).

**Effort**: Medium (add conjuncts to the boss)

**Recommend**: Consider

---

### 8. No transfer moment in the world conclusion

**What**: The plan requires a transfer moment for every lecture world. L08's conclusion discusses what was learned and previews W6, but it never asks the learner to restate a result in plain English or connect to paper-proof reasoning. The "In plain language" sentences in individual levels are good, but the world-level conclusion should have a transfer prompt.

**Why**: Transfer is layer 5 of the course's layered model. The W5 plan has coverage items N1 (I), N1 (S), N1 (G) for notation, but no explicit T-items. The conclusion could at least seed transfer: "In ordinary mathematics, we write {1, 2, 3} and never think about how the set is built. But the construction matters for proofs: when you need to show something about every element, you peel elements off with insert."

**Where**: L08 conclusion.

**Effort**: Low (add a paragraph to the conclusion)

**Recommend**: Yes

---

### 9. `Finset.cons` level (L05) doesn't show why `cons` is actually useful

**What**: L05 proves `cons 1 {2} h = {1, 2}` using `cons_eq_insert`. The conclusion says `cons` is useful "in induction on finsets where you add one element at a time." But the level never demonstrates this advantage. The learner sees `cons` as a strictly worse `insert` (more work, same result).

**Why**: W10 will use `Finset.induction_on`, which produces goals involving `cons`. If L05 gave even a brief worked example (in the introduction or conclusion) showing what a `Finset.induction_on` step looks like -- "the induction step gives you `s` and `a ∉ s`, so the finset is `cons a s h`" -- the learner would understand *why* they are learning `cons`. Without this, `cons` feels like trivia.

**Where**: L05 conclusion.

**Effort**: Low (add a motivating paragraph showing a `Finset.induction_on` goal snippet)

**Recommend**: Consider

---

### 10. The `Color` type in L06 is defined locally but not connected to anything

**What**: L06 defines `inductive Color where | red | green | blue deriving DecidableEq, Repr`. This is the only appearance of a custom type in the entire world. It appears, is used for one `decide` call, and disappears.

**Why**: A custom type is a good teaching opportunity, but the current use is too shallow. The learner sees `Color` as a throwaway. Two improvements: (a) Use `Color` again in the boss (suggestion #7), which would make it feel like a real part of the world's toolkit. (b) Add a brief remark in L06 about what `deriving Repr` does (it's on the same line but never explained). Neither is critical, but (a) would make the world feel more cohesive.

**Where**: L06 and L08.

**Effort**: Low

**Recommend**: Consider

---

## Overall impression

The world has a clear arc from `empty` through `singleton` to `insert` to `cons`, with two conceptual levels (DecidableEq, Finset vs Set) and a boss. The prose quality is high: introductions are well-structured, conclusions consistently include "In plain language" translations, and the DefinitionDocs are informative. The level ladder follows the plan faithfully in spirit if not always in letter.

The single most important improvement is **suggestion #1 combined with #5**: L02 should introduce `Finset.singleton` as a definition (with `NewDefinition` and `DefinitionDoc`), prove `singleton 5 = insert 5 empty` to connect the constructors, and then prove `{5}.card = 1`. This fills the most concrete gap (a plan-required definition that is simply absent) and also addresses the related issue of L02 being a pure `decide` level.

The second priority is **suggestion #4**: L07 should actually demonstrate the Finset/Set confusion rather than just discussing it. A misconception level that only tells is pedagogically weaker than one that shows.
