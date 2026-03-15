# W20 ThreeFiniteness -- Enrichment Review (Round 1)

## Ranked suggestions

### 1. Missing reverse direction: from `Set.Finite` back to `Fintype`

**What**: Add a level (or expand L04) showing `Set.Finite.fintype` or `Set.Finite.fintypeCoe` -- the fact that a `Set.Finite` proof can *produce* a `Fintype` instance on the subtype, closing the loop in the other direction.

**Why**: The world currently presents the conversions as primarily one-directional: `Fintype` implies `Set.Finite` (L02), `Finset` implies `Set.Finite` (L03), and `Set.Finite` can produce a `Finset` (L04). But the mathematically critical reverse direction -- that `Set.Finite s` gives you a `Fintype` instance on `{ x // x in s }` -- is never shown. This is arguably the most important conversion in practice, because it unlocks `Finset.sum` and `Finset.prod` over a set known only to be finite. Without it, the learner has an incomplete mental model of the conversion graph. The conclusion's diagram in L06 shows a one-directional pipeline; the actual relationship is a cycle, and the world should show that.

**Where**: New level between L04 and L05, or expand L04 with a second proof goal.

**Effort**: High (new level).

**Recommend**: Yes.

---

### 2. No subset finiteness lemma (`Set.Finite.subset`)

**What**: Include a level showing that a subset of a finite set is finite: `Set.Finite.subset : t.Finite -> s <= t -> s.Finite`.

**Why**: This is the single most-used `Set.Finite` lemma in real formalization. The world introduces `Set.Finite` with concrete literal sets (L01) and `Set.univ` (L02), but never shows the structural fact that finiteness propagates to subsets. A learner leaving this world will know how to prove specific sets are finite but not how to reason about finiteness abstractly. This is a major gap in the proof-move layer: "propagate finiteness to subsets" is a move that should be isolated and practiced.

**Where**: New level after L02 (where `Set.finite_univ` is introduced), before the `Finset` contrast level.

**Effort**: High (new level).

**Recommend**: Yes.

---

### 3. No concrete example of the three notions applied to the same object

**What**: Add a level (or expand an existing one) where the learner works with a single concrete type (e.g., `Fin 3` or `Bool`) and proves finiteness in all three senses in one place: `Set.Finite`, `Fintype`, and `Finset`.

**Why**: The world introduces each notion in isolation (L01: `Set.Finite` for `{1,2,3} : Set Nat`; L02: `Set.finite_univ` for `Bool`; L03: `Finset.finite_toSet` for `{1,2,3} : Finset Nat`). The types and sets differ across levels, making it harder to compare the notions directly. A single level that uses one object (say `Bool` or `Fin 3`) and asks the learner to express its finiteness in all three forms would crystallize the distinction. This is a concrete example gap -- the abstract comparison tables are present but there's no single worked example that makes the contrast visceral.

**Where**: New level after L03 (after all three notions are introduced), or integrate into L03's conclusion with a concrete side-by-side.

**Effort**: Medium (could be a conclusion expansion) to High (new level).

**Recommend**: Yes.

---

### 4. L01 teaches `Set.finite_insert` as an `iff` but the proof uses `Set.toFinite`

**What**: Either add a second proof obligation in L01 that forces the learner to actually use `Set.finite_insert` step by step, or restructure L01 so the first hint guides toward the structural proof before mentioning `Set.toFinite`.

**Why**: L01's introduction carefully explains `Set.finite_insert` and the idea of peeling elements from `{1,2,3} = insert 1 (insert 2 {3})`. But the model solution and the first hint both offer `Set.toFinite _` as an immediate alternative that bypasses everything just taught. The learner who tries `Set.toFinite _` first (which is natural after reading the hint) never practices the structural decomposition at all. The structural proof IS the lesson -- the one-liner is a convenience fact. If both are presented equally, the structural one will always lose. Either make L01 force the structural proof (disable the one-liner or save it for a remark), or split into two subgoals: (a) prove `{3}.Finite` using `Set.finite_singleton`, (b) prove `{1,2,3}.Finite` using `Set.finite_insert`.

**Where**: L01.

**Effort**: Medium (restructure the level).

**Recommend**: Yes.

---

### 5. The conversion graph is never drawn explicitly for the learner

**What**: Add a visual conversion diagram to L03's conclusion or as part of a "map" level, showing all six directed edges between the three notions (and which lemma provides each edge).

**Why**: L06's conclusion has a partial chain diagram for the boss proof, but the world never shows the full conversion graph as a single picture. The learner is accumulating lemmas (`Set.finite_univ`, `Finset.finite_toSet`, `Set.Finite.toFinset`, `Set.Finite.toFinset_eq_toFinset`, `Set.toFinset_univ`, `Set.Finite.mem_toFinset`) without a single map connecting them. A diagram in L03's conclusion (after all three notions are introduced) would serve as a reference for the remaining three levels. Something like:

```
Fintype --finite_univ--> Set.Finite --toFinset--> Finset
   ^                                                |
   |                    finite_toSet                |
   +--------- Finset.univ <-------------------------+
```

This is the kind of "unnamed strategy" enrichment: the world uses a conversion strategy but never names the graph.

**Where**: L03 conclusion or a new brief "conversion map" level.

**Effort**: Low (conclusion text addition) to Medium (new level).

**Recommend**: Yes.

---

### 6. C1 misconception ("Finset is not Set") is claimed but never surfaced

**What**: Add a level or a worked remark showing that `Finset` and `Set` are truly different types, and that applying a `Set` lemma to a `Finset` (or vice versa) produces a type error.

**Why**: The plan tags L05 with `C1 (R)` (reinforcement of the "Finset is not Set" misconception), but L05 does not actually demonstrate the misconception. It shows that two `toFinset` functions agree and presents a "when to use which" table, but it never shows a failed attempt -- e.g., trying `Set.mem_union` on a `Finset` and getting a type error. The misconception was first warned in W5 and is supposed to be reinforced here. Without an actual demonstration of the confusion, the reinforcement is hollow. Even a "try this and see what goes wrong" remark in a hint would suffice.

**Where**: L05 (or a new level between L03 and L04).

**Effort**: Medium (add a failed-attempt remark or a small "what goes wrong" subgoal).

**Recommend**: Yes.

---

### 7. `Set.Finite.toFinset` cardinality lemma missing

**What**: Introduce `Set.Finite.toFinset_card` or the equivalent fact that `h.toFinset.card = s.toFinset.card` (or directly that `h.toFinset.card` agrees with the expected cardinality).

**Why**: L04 introduces `Set.Finite.toFinset` and `Set.Finite.mem_toFinset` but says nothing about cardinality of the resulting finset. The boss (L06) does a 4-step rewrite chain to compute `Set.finite_univ.toFinset.card = 4`, but never mentions whether there's a direct shortcut. If `Set.Finite.toFinset_card_eq` or a similar lemma exists, the learner should know about it. If it doesn't exist (and the chain is necessary), that fact itself is worth remarking on in L04's conclusion: "Note that there is no single lemma for the cardinality of `h.toFinset` -- you need to chain through `Set.toFinset` and `Finset.univ`."

**Where**: L04 conclusion or L06 conclusion.

**Effort**: Low (a sentence in the conclusion).

**Recommend**: Consider.

---

### 8. No "why three notions?" motivation at the meta level

**What**: Add a sentence or two in L01's introduction explaining *why* Lean/Mathlib has three notions of finiteness, rather than just presenting it as a fact.

**Why**: The introduction lists the three notions and says "each serves a different purpose," but never explains the design rationale. A learner might wonder: why not just use `Finset` for everything? The answer involves the Prop/data distinction, computability, and the type-class system's role. Even one sentence like "Lean separates these because `Set.Finite` lives in `Prop` (erased at runtime), `Fintype` is data that the type-class system manages automatically, and `Finset` is fully computable data you construct by hand" would ground the trichotomy in Lean's design philosophy.

**Where**: L01 introduction.

**Effort**: Low (a sentence or two).

**Recommend**: Consider.

---

### 9. Boss proof is linear -- no branching or decision-making

**What**: Redesign the boss so the learner must choose which conversion path to take, rather than following a prescribed 4-step chain.

**Why**: L06 is a conjunction of two parts, each with a linear chain of rewrites. The hints walk the learner through every step. There is no decision point where the learner must figure out *which* conversion to apply. A better boss might give a goal where two conversion paths are possible and the learner must choose -- e.g., "prove `(↑({0, 1, 2} : Finset (Fin 3)) : Set (Fin 3)).Finite` and `Set.finite_univ.toFinset = (Finset.univ : Finset (Fin 3))`" where the first part could go via `Finset.finite_toSet` directly or via `Set.finite_univ`, and the second part requires the chain. This would test understanding, not just memorization of the rewrite sequence.

**Where**: L06.

**Effort**: Medium (redesign the boss statement).

**Recommend**: Consider.

---

### 10. No foreshadowing of `Finsupp` or permutations

**What**: Add a sentence to L06's conclusion connecting the three-notions framework to the next worlds (W21: Finsupp, W22: Permutations).

**Why**: L06's conclusion says "The next worlds build on these foundations to work with finitely supported functions (`Finsupp`), permutations..." but doesn't explain *how* the three-notions framework is relevant. For example: "When you define `Finsupp`, you will need `Finset` for the support and `Set.Finite` to reason about it abstractly. When you work with permutations, `Fintype` will let you count them." This would seed vocabulary and make the forward reference actionable rather than vague.

**Where**: L06 conclusion.

**Effort**: Low (2-3 sentences).

**Recommend**: Consider.

---

## Overall impression

The world is clearly structured with a logical progression: introduce each notion in isolation (L01-L03), show conversions (L04-L05), then integrate (L06). The comparison tables are well-designed and the "plain language" summary sentences at the end of each conclusion are a nice pedagogical touch. The disabled tactic list is consistent across all levels.

The single most important improvement is **suggestion #1**: the missing reverse conversion from `Set.Finite` back to `Fintype`. Without it, the learner's mental model of the conversion graph has a critical gap -- they understand going "down" (from data-rich to data-poor) but not "up" (from a finiteness proof back to computable data). This is the conversion that matters most in practice, and its absence means the world's promise ("can convert between them") is only partially fulfilled.

Secondary priorities are **suggestion #2** (subset finiteness -- the most common `Set.Finite` proof move in practice) and **suggestion #4** (L01's structural proof being eclipsed by the one-liner).
