# W5 FinsetConstructors -- Enrichment Review (Round 2)

## R1 disposition

Before new suggestions, here is the status of each R1 item after the changes made between rounds.

| R1 # | Item | Status | Notes |
|-------|------|--------|-------|
| 1 | L02 never introduces `Finset.singleton` | **Still open** | L02 now uses `card_singleton` rewrite, which is an improvement. But `Finset.singleton` is still not declared via `NewDefinition` and has no `DefinitionDoc`. The learner rewrites using a lemma about `singleton` without knowing what `singleton` is. |
| 2 | `decide` inconsistency across levels | **Resolved** | `decide` is now disabled on all levels except L07, and L07 uses it intentionally for a concrete membership check after `use`. The policy is consistent. |
| 3 | L02 and L06 are pure `decide` levels | **Resolved** | L02 now uses `rw [Finset.card_singleton]` -- a genuine proof move. L06 uses `rfl` -- a legitimate tactic for a definitional equality. Neither is a "press the button" level anymore. |
| 4 | L07 diverges from plan (should show failed Set lemma) | **Partially addressed** | L07 intro now shows a `Set.mem_union` type error example in prose, and the conclusion reinforces the Set/Finset namespace separation. The *goal* is still `Finset.Nonempty`, which does not directly exercise the Finset-vs-Set confusion. The prose improvement is good; the goal mismatch with the plan's intent persists. See suggestion #3 below. |
| 5 | No `singleton_eq_insert_empty` derivation | **Still open** | L02 still does not prove the relationship between `singleton`, `insert`, and `empty`. The three constructors are presented in sequence (L01, L02, L03) but never connected. |
| 6 | No duplicate-insert experience | **Not expected in this round** | Plan places this in W6 L06. Acceptable to defer. |
| 7 | Boss doesn't test DecidableEq or Finset-vs-Set | **Still open** | L08 boss still tests only L01-L05 skills. L06 and L07 remain unintegrated. See suggestion #4. |
| 8 | No transfer moment in conclusion | **Resolved** | L08 conclusion now has a substantial "Transfer to paper proofs" section connecting Lean's explicit construction mechanism to paper math conventions and explaining the computational reality of `DecidableEq`. Well done. |
| 9 | L05 doesn't show why `cons` is useful | **Still open** | L05 conclusion mentions induction as the motivation but does not show what a `Finset.induction_on` step looks like. The motivation remains abstract. |
| 10 | `Color` type not connected to anything | **Still open** | `Color` is defined in L06 and never reused. Minor. |

---

## New ranked suggestions

### 1. L02 still missing `NewDefinition Finset.singleton` and `DefinitionDoc`

**What**: L02 uses `Finset.card_singleton` in its proof -- a lemma whose name contains `singleton` -- but `Finset.singleton` itself is never formally introduced. There is no `NewDefinition Finset.singleton` and no `DefinitionDoc Finset.singleton` in any level of this world.

**Why**: This was R1 suggestion #1 and remains the most concrete gap. The learner encounters `card_singleton` and reads about singletons in prose, but the formal definition is never entered into their inventory. When `Finset.mem_singleton` appears in W6 L03, the learner will see a lemma about a definition they were never formally taught. The `DefinitionDoc` in L01 for `Finset` *mentions* `Finset.singleton a` in the usage list, but that is a passing reference in another definition's doc, not a formal introduction.

The fix is small: add `NewDefinition Finset.singleton` to L02 and add a `DefinitionDoc Finset.singleton` block. No change to the proof goal is needed.

**Where**: L02

**Effort**: Low (add two doc blocks and one `NewDefinition` line)

**Recommend**: Yes

---

### 2. L02 should connect singleton to insert-on-empty (R1 #5 still open)

**What**: Prove `Finset.singleton 5 = insert 5 ∅` as a sub-goal or as a separate statement before the cardinality proof, showing that singleton is derivable from `empty` and `insert`.

**Why**: The three constructors `empty`, `singleton`, and `insert` form a hierarchy: `singleton a = insert a empty`. This structural relationship is mentioned in L02's prose ("Under the hood, `{5}` is the same as `insert 5 ∅`") but never proved. Making it a goal would (a) connect L01 to L02, (b) prepare for L03 where `insert` is formally introduced, and (c) give the learner a concrete experience of definitional equality on finset constructors before the `card_singleton` rewrite. The proof is `rfl`.

**Where**: L02. Add as a first conjunct: `Finset.singleton 5 = insert 5 (∅ : Finset Nat) ∧ ({5} : Finset Nat).card = 1`. The first half is `rfl`, the second uses `rw [Finset.card_singleton]`.

**Effort**: Medium (modify the statement to a conjunction, add hints for the first conjunct)

**Recommend**: Yes

---

### 3. L07's goal still does not exercise the Finset-vs-Set distinction

**What**: The L07 intro now shows a type error example from `Set.mem_union` applied to a `Finset`, which is a meaningful improvement. But the actual proof goal (`Finset.Nonempty {1,2,3}`) has nothing to do with Finset-vs-Set. The learner proves nonemptiness via `use 1; decide` -- a pattern that exercises existential witnesses and decidability, not type confusion between `Set` and `Finset`.

**Why**: This is a "tell not show" gap. The prose tells the learner about the distinction, but the proof goal does not exercise it. A learner who solves L07 has practiced `use` and `decide`, not Finset-vs-Set awareness. However, this is a pedagogical design choice with tradeoffs: actually *producing* a type error in a proof goal is hard to do in the game framework (the learner needs a goal that *compiles*). The current approach -- showing the error in prose, then proving a legitimate Finset-specific goal -- is defensible if the `Finset.Nonempty` goal is framed as "this is a Finset-specific concept that has no direct `Set` analogue."

The conclusion *does* say "If you had a `Set` instead of a `Finset`, you would use `Set.Nonempty` and its own API." This connects the goal to the lesson. The gap is smaller than in R1 because the prose is now much better.

**Where**: L07 intro/conclusion. If modifying the goal is not desired, at minimum add a sentence to the intro: "The concept `Finset.Nonempty` is Finset-specific. If you tried `Set.Nonempty` on a `Finset`, you would get a type error -- just as `Set.mem_union` fails on finsets."

**Effort**: Low (add a sentence) or High (redesign the goal)

**Recommend**: Consider -- the current version is acceptable if the prose framing is tightened to explicitly connect the goal to the lesson. The prose is already most of the way there.

---

### 4. Boss (L08) still does not integrate L06 (DecidableEq) or L07 (Finset vs Set)

**What**: L08 tests notation desugaring (L03/L04), `cons_eq_insert` (L05), `card_insert_of_notMem` (new in L08), and `card_singleton` (L02). L06's `DecidableEq` lesson and L07's `Finset.Nonempty` / Finset-vs-Set lesson are not tested.

**Why**: A boss that covers 5 of 7 pre-boss levels leaves two lessons feeling disconnected. The boss redesign added `card_insert_of_notMem` and `card_singleton` as structural cardinality reasoning tools, which is excellent. But the `Color` type from L06 is never seen again, and `Finset.Nonempty` from L07 is never reused.

A fourth conjunct such as `({Color.red, Color.blue} : Finset Color).card = 2` would integrate L06's `DecidableEq` lesson (this only compiles because `Color` has `DecidableEq`) and give the learner a second instance of the `card_insert_of_notMem` + `card_singleton` peeling pattern on a different type. Alternatively, a `Finset.Nonempty` sub-goal on the main finset would integrate L07.

However, this needs care: `Color` is defined locally in L06, so L08 would need its own copy of the `Color` inductive (or the world file would need to define it once for both). This is a real implementation cost.

**Where**: L08

**Effort**: Medium (add a conjunct + handle the `Color` type scoping)

**Recommend**: Consider -- the boss is already strong with three conjuncts. Integrating L06/L07 would make it a true capstone, but the `Color` scoping issue adds friction.

---

### 5. L05 conclusion could show a `Finset.induction_on` goal snippet

**What**: L05's conclusion says `cons` is useful "in induction on finsets where you add one element at a time and need to know it was not already there." But it never shows what this looks like.

**Why**: The motivation for `cons` is entirely abstract. Adding 2-3 lines of pseudocode to the conclusion would make it concrete:

```
-- When you do induction on finsets, the step case gives you:
-- s : Finset α, a : α, h : a ∉ s
-- and the finset is (cons a s h).
-- The non-membership proof h is exactly what cons needs.
```

This takes the claim "cons is useful for induction" from handwaving to concrete preview. The learner does not need to understand induction yet -- just seeing the shape of the goal makes the motivation real.

**Where**: L05 conclusion

**Effort**: Low (add a small code block to existing conclusion text)

**Recommend**: Yes

---

### 6. L04 misses an opportunity to show that finset notation is order-independent

**What**: L04's conclusion says "finsets have no order, so `{1, 2, 3} = {3, 1, 2}`" but this is stated as prose, never proved. The level only proves `{1, 2, 3} = insert 1 (insert 2 {3})`, which is a notation-desugaring fact, not an order-independence fact.

**Why**: Finset order-independence is a foundational property that distinguishes finsets from lists. The learner has spent W3 (ListBasics) learning that list order matters. Proving `{1, 2, 3} = {3, 1, 2}` would be a powerful contrast. However, this proof is non-trivial: it requires `Finset.ext` or `decide`, and `Finset.ext` is not taught until W7. So the proof would need to be `decide` (currently disabled) or `Finset.ext_iff` (not yet in inventory).

Given the disabled-tactic constraints and the fact that `ext` is a W7 topic, this is better as a forward reference than a level goal.

**Where**: L04 conclusion

**Effort**: Low (the prose already says it; could strengthen by adding "you will prove this formally in World 7 using `ext`")

**Recommend**: Consider -- adding the forward reference sentence is worthwhile, but making it a proof goal would require tools the learner does not yet have.

---

### 7. `Finset.card_empty` is referenced but never formally introduced

**What**: L02's conclusion mentions `Finset.card_empty` ("the lemma `Finset.card_empty` says `(∅ : Finset α).card = 0`") but it is never a `NewTheorem` in any level of this world. Meanwhile, `Finset.card_singleton` and `Finset.card_insert_of_notMem` are both formally introduced.

**Why**: The three cardinality lemmas form a complete base for computing finset cardinality: `card_empty` (base for ∅), `card_singleton` (base for {a}), and `card_insert_of_notMem` (recursive step). The boss uses `card_singleton` as its base case, so `card_empty` is not strictly needed. But mentioning a theorem by name in prose without adding it to the inventory is an inconsistency that could confuse the learner who tries to use it in a later world and wonders why it is not in their theorem panel.

**Where**: L01 or L02. Add `NewTheorem Finset.card_empty` and a `TheoremDoc` for it.

**Effort**: Low (add two doc blocks and one line)

**Recommend**: Consider -- it is not load-bearing for this world, but the inconsistency between mentioning it in prose and not adding it to the inventory is a small quality issue.

---

## Overall impression

The world has improved significantly since R1. The three most important changes -- L02 now uses `card_singleton` rewrite instead of `decide`, L06 demonstrates the `DecidableEq` error in prose, and L08's boss has been redesigned with structural cardinality reasoning -- have addressed the worst pedagogical gaps. The `decide` policy is now consistent (disabled everywhere except L07 where it serves a specific purpose). The transfer section in L08's conclusion is strong. The prose quality throughout is high, with clear "In plain language" sections and well-structured introductions.

The single most important remaining improvement is **suggestion #1**: adding `NewDefinition Finset.singleton` and a `DefinitionDoc` to L02. This is a small change with clear value -- the definition is already used implicitly (via `card_singleton`) and will be referenced explicitly in W6. Closely related is **suggestion #2**: adding a `singleton 5 = insert 5 ∅` sub-goal to connect the constructor hierarchy. Together, these two changes would make L02 the strongest level in the world rather than just a good one.
