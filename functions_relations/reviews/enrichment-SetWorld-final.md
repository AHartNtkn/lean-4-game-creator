# Enrichment Review: SetWorld

**Course**: functions_relations
**World**: SetWorld (W01)
**Levels reviewed**: L01–L09

---

## Ranked Suggestions

### 1. Add a disjunction membership level

**What**: Add a level proving membership in a set with an `∨` predicate, e.g., `5 ∈ {n : ℕ | n < 3 ∨ n > 4}` using `right`.

**Why**: L08's conclusion explicitly presents a table claiming `P x ∨ Q x` membership uses `left` or `right`, but the world never teaches or uses either tactic. The player reads "use `left` or `right`" in the conclusion and has never done it. This is a promise the world makes and does not keep. It also means the logical connective coverage is incomplete: `∧` gets a full level (L08) but `∨` gets only a table entry.

**Where**: New level between L08 and L09 (current boss). Or modify L08 to be conjunction, add L09 as disjunction, push boss to L10.

**Effort**: High (add a new level)

**Recommend**: Yes — the world's own conclusion advertises this pattern. Not teaching it is a gap.

---

### 2. Show sets work on types other than ℕ

**What**: Include one level (or modify an existing one) that uses a type other than `ℕ` — e.g., `"hello" ∈ {s : String | s.length < 10}` or `true ∈ {b : Bool | b = true}`.

**Why**: All 9 levels use `ℕ`. The world introduction says "A set of natural numbers is just a function..." and the learner may silently conclude sets are a natural-number concept. One non-ℕ example would make the `Set α` generality concrete and prevent this misconception from forming.

**Where**: Could be a brief early level (after L02, showing set-builder works on any type) or folded into L08 as the compound-predicate example.

**Effort**: Medium (modify existing level or add a short one)

**Recommend**: Yes — the generality of `Set α` is the core insight and currently lacks any demonstration beyond ℕ.

---

### 3. Finite enumerated sets as disjunctive predicates

**What**: A level showing that the informal set `{1, 3, 5}` corresponds to `{n : ℕ | n = 1 ∨ n = 3 ∨ n = 5}`, with a membership proof.

**Why**: Most students' first association with "set" is listing elements: `{1, 2, 3}`. This world never connects that informal notion to the predicate definition. Showing that a finite listing is just a chain of disjunctions would bridge the gap between informal and formal set concepts and reinforce that predicates subsume enumeration. This also naturally introduces `left`/`right` (connecting to suggestion #1).

**Where**: New level, or could be combined with the disjunction level from suggestion #1.

**Effort**: Medium (one new level that could merge with #1)

**Recommend**: Consider — partially overlaps with #1, but the pedagogical point (enumerated sets ARE disjunctive predicates) is distinct and worth making.

---

### 4. Name the proof pattern explicitly

**What**: The conclusion of L05 identifies the "membership reduction pattern" — unfold set notation, work with the predicate, close. This pattern is used in every level but is only named once, in passing, in L05's conclusion. Give it a prominent name early (e.g., "the membership reduction") and reference it by name in subsequent conclusions.

**Why**: Naming a recurring strategy makes it transferable. When the learner encounters `x ∈ f '' s` in ImageWorld, they should think "membership reduction — unfold, work with the predicate." If the pattern has a name they've seen four times, this transfer is more likely.

**Where**: L02 conclusion (first instance of the full pattern), then referenced in L03, L05, L08, L09 conclusions.

**Effort**: Low (modify conclusion text in existing levels)

**Recommend**: Yes — this is the world's central proof strategy and deserves a name that carries forward.

---

### 5. L09 boss: note the iff / set equality connection

**What**: In L09's conclusion (or introduction), note that `hp` and `hq` together give `∀ n, p n ↔ Even n`, which by extensionality means `{n | p n} = {n | Even n}` as sets. Don't prove it — just state it and say "you'll learn to prove this in SubsetWorld."

**Why**: The boss already has both directions of an iff but never names this. Pointing it out explicitly plants the seed for `ext` and set equality, giving the learner a concrete forward reference. It also elevates the boss from "do two things" to "see a deeper structure."

**Where**: L09 conclusion, 1–2 sentences.

**Effort**: Low (add sentences to conclusion)

**Recommend**: Yes — this is a derivable result (set equality from two subset directions) presented as two separate tasks. Naming the connection is a teaching moment.

---

### 6. Mention `Odd` as the natural counterpart to `Even`

**What**: In L05's conclusion (or as a brief remark in L04's conclusion), mention that Lean also has `Odd n` defined as `∃ r, n = 2 * r + 1`, and that the proof `3 ∉ {n | Even n}` is essentially proving 3 is odd.

**Why**: The learner proves 3 is not even but never sees what 3 IS. Mentioning `Odd` gives vocabulary and makes the mathematical picture complete. It also sets up a possible "what if" moment: "could we define `{n | Odd n}` as the complement of `{n | Even n}`?" — foreshadowing complement/set operations.

**Where**: L05 conclusion, 1–2 sentences.

**Effort**: Low (add sentences to conclusion)

**Recommend**: Consider — nice mathematical context but not essential for the world's goals.

---

### 7. Contrast `show` and `change`

**What**: Note (in L02's conclusion or as a remark) that `show` works on the goal and `change` works on hypotheses, and that both convert to definitionally equal forms. No need to teach `change` formally yet.

**Why**: `show` is introduced as a key tool, and the learner will need `change` on hypotheses in later worlds. A brief mention now ("there is a counterpart `change` for hypotheses — you'll meet it later") costs nothing and primes the learner.

**Where**: L02 conclusion, 1 sentence.

**Effort**: Low (one sentence)

**Recommend**: Consider — useful foreshadowing but low impact for this world.

---

### 8. Address "sets are not types" more directly

**What**: The DefinitionDoc for `Set` in L01 says "Set α is not the same as a type α" but no level makes this distinction experiential. A brief remark or a carefully constructed level could show the difference — e.g., "you can't write `(3 : Set ℕ)` — that's a type error" or "you need the coercion ↥ to treat a set as a type."

**Why**: The sets-are-not-types confusion is listed as a misconception in the plan. The doc mentions it but the levels never test or reinforce it. Later worlds (SubtypeWorld, EquivWorld) depend on the learner understanding this distinction.

**Where**: L01 conclusion or a short remark level.

**Effort**: Low–Medium (remark in conclusion or short demonstration level)

**Recommend**: Consider — important conceptually, but may be premature to make experiential in World 1. The doc mention may be sufficient for now; SubtypeWorld is where this becomes load-bearing.

---

## Overall Impression

SetWorld does its core job well: it methodically introduces `Set α = α → Prop`, builds from trivial membership through negation and existentials to compound predicates, and culminates in a boss that requires combining all the moves. The introductions and conclusions are clear and consistently reinforce the "sets are predicates" message. The hint scaffolding provides good fallback paths.

The single most important improvement is **adding a disjunction level** (suggestion #1). The world's own conclusion in L08 promises the learner they can handle `∨` predicates with `left`/`right`, but no level teaches this. Adding it would complete the logical connective coverage, introduce two important tactics (`left`/`right`), and make the L08 conclusion's table honest. The second priority is **naming the membership reduction pattern** (#4) — it costs almost nothing and makes the world's central insight portable to every subsequent world.
