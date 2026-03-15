# W5 FinsetConstructors -- Enrichment Review (Round 3)

## Changes since R2

The main change was the addition of L08 (CardinalityPeeling) as a practice level for `card_insert_of_notMem`. The previous boss (old L08) was renumbered to L09. This means `card_insert_of_notMem` is now introduced in L08 with a scaffolded exercise before the boss uses it in L09. The world is now 9 levels.

## R2 disposition

| R2 # | Item | Status | Notes |
|-------|------|--------|-------|
| 1 | L02 missing `NewDefinition Finset.singleton` and `DefinitionDoc` | **Still open** | L02 still has no `NewDefinition Finset.singleton` and no `DefinitionDoc Finset.singleton`. The learner uses `Finset.card_singleton` — a lemma *about* `singleton` — without `singleton` itself ever being formally introduced. This is a concrete inventory gap that affects W6 L03 (`mem_singleton`). |
| 2 | L02 should connect singleton to insert-on-empty | **Still open** | L02's introduction mentions "Under the hood, `{5}` is the same as `insert 5 ∅`" but the proof goal does not exercise this relationship. The three constructors (`empty`, `singleton`, `insert`) remain unconnected. |
| 3 | L07's goal does not exercise Finset-vs-Set | **Acceptable** | L07's prose now clearly connects `Finset.Nonempty` to the Finset-vs-Set distinction: the intro shows a `Set.mem_union` type error, and the conclusion contrasts `Set.Nonempty` with `Finset.Nonempty`. The goal, while not directly exercising type confusion, gives the learner a Finset-specific concept (`Finset.Nonempty`) that has no `Set` analogue with the same API. The prose framing is now strong enough that the goal mismatch is pedagogically acceptable. **Closing this item.** |
| 4 | Boss does not integrate L06/L07 | **Acceptable with the new L08** | The boss (now L09) integrates L01–L05 via notation/cons/insert and L08 via `card_insert_of_notMem`. L06 (DecidableEq) and L07 (Finset.Nonempty) remain unrepresented, but the boss is now a 3-conjunct cardinality reasoning exercise with genuine multi-step structure. Adding a fourth conjunct for `Color` would require scoping the inductive type across levels (implementation friction) and would make the boss overlong. The current boss is a strong capstone for the constructor/cardinality skills. **Closing this item.** |
| 5 | L05 conclusion should show `Finset.induction_on` snippet | **Still open** | L05's conclusion says `cons` is useful "in induction on finsets where you add one element at a time and need to know it was not already there" but does not show what the induction step looks like. A 3-line code snippet would make this concrete. |
| 6 | L04 order-independence forward reference | **Acceptable** | L04's conclusion already says "finsets have no order, so `{1, 2, 3} = {3, 1, 2}`." Adding a forward reference to W7 `ext` would be nice but is not a gap. **Closing this item.** |
| 7 | `Finset.card_empty` referenced but not formally introduced | **Now more relevant** | L08's conclusion explicitly lists `card_empty` as one of the three peeling lemmas ("base case for ∅") alongside `card_singleton` and `card_insert_of_notMem`, both of which are formally introduced. `card_empty` remains the only one without `NewTheorem` and `TheoremDoc`. The inconsistency is now more visible because all three are named in the same paragraph. |

---

## New ranked suggestions

### 1. L02 still missing `NewDefinition Finset.singleton` and `DefinitionDoc`

**What**: Add `NewDefinition Finset.singleton` and a `DefinitionDoc Finset.singleton` block to L02.

**Why**: This is the third round where this item has been flagged. It is the most concrete gap in the world. The learner encounters `card_singleton` (L02), `cons_eq_insert` applied to singletons (L05), and `card_singleton` again in the boss (L09), all without `Finset.singleton` ever being in their inventory. In W6 L03, `Finset.mem_singleton` appears — a lemma about a definition the learner was never formally taught. The fix requires adding two blocks and one line; no proof changes are needed.

**Where**: L02

**Effort**: Low (add `NewDefinition Finset.singleton` line and a `DefinitionDoc Finset.singleton` block)

**Recommend**: Yes

---

### 2. L02 should prove the singleton-insert-empty connection

**What**: Change L02's statement to a conjunction: `Finset.singleton 5 = insert 5 (∅ : Finset Nat) ∧ ({5} : Finset Nat).card = 1`, or add a separate sub-goal proving `Finset.singleton 5 = insert 5 ∅`.

**Why**: Also the third round. The introduction says "Under the hood, `{5}` is the same as `insert 5 ∅`" but the learner never proves it. This derivable relationship — that `singleton` is just `insert` on `empty` — connects L01 to L02 to L03 in a way that the current isolated `card_singleton` rewrite does not. The first conjunct is `rfl`; it introduces no new difficulty but gives the learner a structural insight about how the constructors compose. Combined with suggestion #1 (making `Finset.singleton` a named definition), this would make L02 the level that formally establishes the singleton as a concept with a name, a relationship to `insert`/`empty`, and a cardinality fact.

**Where**: L02

**Effort**: Medium (modify Statement to a conjunction, add `constructor` hint, add hint for the `rfl` sub-goal)

**Recommend**: Yes

---

### 3. L05 conclusion should show a `Finset.induction_on` goal snippet

**What**: Add a concrete code block to L05's conclusion showing what the induction step looks like in a `Finset.induction_on` proof.

**Why**: Second round flagging this. The learner is told `cons` is useful for finset induction but never sees what that looks like. Adding:

```
-- In a Finset.induction_on proof, the step case gives you:
-- ih : P s
-- a : α
-- ha : a ∉ s
-- ⊢ P (cons a s ha)
-- The non-membership proof ha is exactly what cons needs.
```

This takes 5 lines and makes the forward reference concrete. The learner does not need to understand induction — they just need to see that the shape of the goal justifies learning `cons`.

**Where**: L05 conclusion

**Effort**: Low (add a code block to existing text)

**Recommend**: Yes

---

### 4. `Finset.card_empty` should be formally introduced

**What**: Add `NewTheorem Finset.card_empty` and a `TheoremDoc Finset.card_empty` block, either in L01 (where `∅` is introduced) or in L08 (where the peeling pattern is taught).

**Why**: L08's conclusion explicitly names all three peeling lemmas as a complete system: `card_insert_of_notMem` (introduced as `NewTheorem` in L08), `card_singleton` (introduced in L02), and `card_empty`. The first two are in the learner's inventory; the third is mentioned by name but never formally introduced. This creates a situation where the learner reads "these three lemmas let you compute the cardinality of any finset" but can only look up two of them in the theorem panel. Additionally, L02's conclusion references `card_empty` by name: "the lemma `Finset.card_empty` says `(∅ : Finset α).card = 0`."

The natural home is L01 (where `∅` is introduced), as a companion to the `rfl` proof: after showing `Finset.empty = ∅`, mentioning that `(∅).card = 0` is `card_empty` would be a natural transition to L02's `card_singleton`.

Alternatively, L08 is a second natural home, since L08 is where the peeling pattern is explicitly taught and all three lemmas are named.

**Where**: L01 or L08

**Effort**: Low (add `NewTheorem` line + `TheoremDoc` block)

**Recommend**: Yes

---

### 5. L08 could use the full peeling pattern instead of finishing with `decide`

**What**: L08 currently proves `(insert 1 {2, 3}).card = 3` by one `rw [card_insert_of_notMem h]` followed by `decide` for the remaining `{2, 3}.card + 1 = 3`. Consider requiring the learner to peel `{2, 3}` further: `rw [card_insert_of_notMem h₂]` then `rw [card_singleton]`, so the full peeling chain is practiced before the boss.

**Why**: L08's purpose is to teach the peeling pattern. But the learner only peels one layer and then `decide` handles the rest. In the boss (L09), the learner must peel two layers and use `card_singleton`. The jump from "peel once, decide the rest" (L08) to "peel twice, use card_singleton" (L09) is manageable but could be smoother if L08 itself required the full chain. This would also make L08 a better practice level: the learner would execute the complete peeling pattern (`card_insert_of_notMem` → `card_insert_of_notMem` → `card_singleton`) once in a simpler context before doing it in the boss's multi-conjunct setting.

This would require providing two non-membership hypotheses (one for `1 ∉ {2,3}` and one for `2 ∉ {3}`) and changing the hint sequence to guide through all three rewrites.

**Where**: L08

**Effort**: Medium (modify statement to provide two hypotheses, update hints to guide through three rewrites instead of one rewrite + decide)

**Recommend**: Consider — the current version works and the boss provides the full pattern. But having L08 practice the complete chain would make the boss less intimidating and would fully honor L08's title "Cardinality by peeling."

---

### 6. L04 could mention that `{3}` is itself `insert 3 ∅`

**What**: Add a sentence to L04's introduction or hints noting that `{3}` on the right-hand side is `insert 3 ∅`, so the full desugaring is `insert 1 (insert 2 (insert 3 ∅))`.

**Why**: L04 proves `{1, 2, 3} = insert 1 (insert 2 {3})`, but the introduction already shows the full chain including `insert 3 ∅`. The hints say "both sides desugar to `insert 1 (insert 2 (insert 3 ∅))`." So the connection is made. However, a learner might wonder why the right-hand side uses `{3}` rather than `insert 3 ∅` — the answer is that `{3}` is notation for `insert 3 ∅`, which the learner was told in L02 but might not have internalized. A brief parenthetical in the hint — "(recall that `{3}` is itself `insert 3 ∅`)" — would reinforce this without adding a new level.

**Where**: L04 hints

**Effort**: Low (add a parenthetical)

**Recommend**: Consider — the information is already present in L02's intro and L04's own hints. This is reinforcement, not a gap.

---

## Overall impression

The world has improved substantially across the three review rounds. The addition of L08 (CardinalityPeeling) was the right structural choice: it gives the learner scaffolded practice with `card_insert_of_notMem` before the boss demands it in a multi-conjunct setting. The `decide` policy is now consistent (disabled everywhere except L07 where it serves a specific purpose). The prose quality is uniformly high — introductions are well-structured, conclusions consistently include "In plain language" summaries, and the transfer section in L09's conclusion is strong. The level ladder from `empty` through `singleton` to `insert` to `cons` to `DecidableEq` to `Finset.Nonempty` to cardinality peeling to the boss is pedagogically sound.

The single most important remaining improvement is **suggestion #1**: adding `NewDefinition Finset.singleton` and `DefinitionDoc` to L02. This is the third consecutive round flagging this gap, the fix is trivially small (two blocks + one line, no proof changes), and the downstream impact is real — W6 L03 uses `mem_singleton` about a definition the learner was never formally introduced to. Closely related is **suggestion #2** (proving `singleton = insert on empty`), which would give L02 genuine structural depth, and **suggestion #4** (introducing `card_empty`), which would complete the peeling lemma triad that L08's conclusion describes. Together, these three low-effort changes would close every concrete gap remaining in the world.
