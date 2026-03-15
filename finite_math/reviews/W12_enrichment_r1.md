# W12 CountingPigeonhole — Enrichment Review (Round 1)

## Ranked suggestions

### 1. Missing planned level: Cardinality of subtypes (L03 in the plan)

**What**: The plan specifies L03 as "Cardinality of subtypes: Count elements of `{ x : Fin 5 // x.val % 2 = 0 }`" (coverage item M14(S)), but the implemented L03 is "Cardinality of Option types" instead. Subtypes are never covered in this world.

**Why**: Subtypes are a fundamentally different type constructor from sums, functions, and options. The plan explicitly includes them because they test a different facet of `Fintype` propagation — the instance for subtypes is less obvious than for sums or options. A learner who can count `α ⊕ β` and `Option α` but not `{ x : α // P x }` has a genuine gap. Furthermore, subtype cardinality requires a different proof strategy (likely involving `Fintype.card_subtype_compl` or `Finset.card_filter`, connecting back to W8/W9 material), which makes it a more interesting pedagogical exercise than `Option`, whose proof is mechanically identical to L01.

**Where**: Add a new level (between current L03 and L04, making it L04 in the new numbering) for subtype cardinality. The Option level (current L03) is fine to keep.

**Effort**: High (new level).

**Recommend**: Yes — this is a plan deviation, and the omitted content is pedagogically important.

### 2. L04 (Nonempty witness) is trivially closable by `exact h`

**What**: The level asks the learner to prove `∃ x, x ∈ s` given `h : s.Nonempty`, and the conclusion even acknowledges that `exact h` works because `Finset.Nonempty` is definitionally `∃ x, x ∈ s`. The intended lesson (`obtain` on existentials) is bypassed.

**Why**: The conclusion's "you could also have used `exact h` directly" makes the level feel like a trick question. The learner who discovers `exact h` first learns nothing about witness extraction. To make the `obtain` pattern genuinely necessary, the goal should require *doing something* with the witness — for example, proving a statement that mentions the extracted element, or producing a value of a different type.

**Where**: L04. Redesign the statement so that the goal is not definitionally equal to the hypothesis. For example: given `s.Nonempty` and `∀ x ∈ s, P x`, prove `∃ x ∈ s, P x`. This forces the learner to destructure `s.Nonempty` with `obtain`, then use the universally quantified hypothesis on the witness, then repackage.

**Effort**: Medium (modify level statement and proof).

**Recommend**: Yes — as written, the level fails to teach its dominant lesson to any learner who tries `exact h` first.

### 3. The "assume injective, derive cardinality bound, contradict" pattern is used three times but never named

**What**: L06, L07, and L10 all use the identical proof pattern: `intro hinj` → `have h := Fintype.card_le_of_injective f hinj` → `rw [Fintype.card_fin, ...] at h` → `omega`. This three-step strategy deserves a name.

**Why**: Naming proof strategies is one of the strongest pedagogical moves available. When a pattern appears three times, articulating it as "the pigeonhole proof pattern" or "the cardinality contradiction pattern" — and explicitly calling it out — helps the learner recognize it in new settings. The conclusion of L06 partially does this ("the proof followed the classic pattern"), but it never gives the pattern a memorable name. The conclusion of L07 compares the two instances in a table, which is good, but still doesn't name the strategy. By L10, the learner should be thinking "this is the cardinality contradiction pattern again" without needing hints.

**Where**: L06 conclusion (name the pattern), L07 conclusion (reinforce the name), L10 introduction (ask the learner to recognize and apply the named pattern).

**Effort**: Low (text changes in introductions/conclusions).

**Recommend**: Yes — naming strategies is a core pedagogical commitment of this course.

### 4. No level connects `Option (Fin n)` to `Fin (n + 1)` for pigeonhole setup

**What**: L03 teaches `Fintype.card_option` and its conclusion says "this will be important for the pigeonhole principle: when we have n+1 objects to place into n boxes, the domain has one more element than the codomain — exactly the relationship between `Option (Fin n)` and `Fin n`." But no subsequent level actually uses `Option` in a pigeonhole argument. L06 uses `Fin 4 → Fin 3`, and L07 uses `Fin (n+1) → Fin n`.

**Why**: The conclusion of L03 creates an expectation that is never fulfilled. The learner is told Option is relevant to pigeonhole, but then pigeonhole is always stated with `Fin`. Either the connection should be made explicit in a level (e.g., a level that proves pigeonhole using `Option (Fin n) → Fin n` instead of `Fin (n+1) → Fin n`), or the L03 conclusion should be softened to avoid creating a dangling thread.

**Where**: Option A (preferred): Add a remark or short exercise in L06 or L07 showing `Fintype.card (Option (Fin n)) = n + 1 = Fintype.card (Fin (n+1))`, making the connection explicit. Option B: Modify L03 conclusion to say "Option adds one element, which is conceptually similar to the n+1 vs n comparison in pigeonhole" without promising a direct application.

**Effort**: Low (add a remark) or Medium (add a bridge exercise).

**Recommend**: Yes — dangling foreshadowing without payoff is a pedagogical anti-pattern.

### 5. L02 (`Fintype.card_fun`) does not connect to the multiplication principle, despite the conclusion claiming to

**What**: The L02 conclusion says "Why $3^2$? Each of the 2 inputs independently chooses from 3 outputs. By the multiplication principle, the total count is $3 \times 3 = 3^2$." But the multiplication principle was never formally introduced; the conclusion uses it informally. The plan places the multiplication principle transfer moment in W12_ex L05, but the learner encounters the phrase here first without context.

**Why**: Using terminology before it is introduced creates confusion. The phrase "multiplication principle" should either be introduced properly (as a named concept) or avoided. Since W12_ex will cover it formally, the cleanest fix is to rephrase L02's conclusion to explain the counting argument without invoking the named principle, then let W12_ex introduce the name.

**Where**: L02 conclusion text.

**Effort**: Low (text edit).

**Recommend**: Consider — the issue is real but minor, since the informal explanation is clear enough.

### 6. No level explores what happens when domain and codomain have equal size

**What**: The world teaches pigeonhole for `|domain| > |codomain|` but never discusses the boundary case `|domain| = |codomain|`. A function `Fin n → Fin n` *can* be injective (e.g., the identity). This is the natural "what if?" question.

**Why**: Exploring the boundary case builds mathematical maturity. After proving that `Fin 4 → Fin 3` cannot be injective, the learner should wonder: "What about `Fin 3 → Fin 3`?" A level that asks the learner to exhibit an injective function `Fin 3 → Fin 3` (or prove the identity is injective) would make the pigeonhole hypothesis feel necessary rather than arbitrary. It also previews the bijection concept.

**Where**: Between current L07 and L08. A level asking "exhibit an injective function `Fin 3 → Fin 3`" or "prove `Function.Injective id`" would serve as a counterpoint to L06-L07.

**Effort**: High (new level).

**Recommend**: Consider — this is a genuine "what if?" opportunity, but the world is already at 10 levels and the plan's W12_ex L02 touches on counting injective functions. It could be deferred to W12_ex.

### 7. L05 (contradiction via cardinality) uses `Finset.card` but the rest of the world uses `Fintype.card`

**What**: L05 works with `Finset.card` (element-level cardinality of a specific finset `s`), while L01-L03 and L06-L10 work with `Fintype.card` (type-level cardinality). The distinction is never explicitly discussed.

**Why**: A learner may be confused about why the API switches from `Fintype.card` to `Finset.card` and back. The two are related by `Fintype.card α = Finset.univ.card` (taught in W11 L03 per the plan), but this connection is not mentioned in L05. A brief remark in the L05 introduction noting "We now work with `Finset.card` (the cardinality of a specific finset `s`) rather than `Fintype.card` (the cardinality of an entire type). Recall from the previous world that `Fintype.card α = Finset.univ.card`" would prevent confusion.

**Where**: L05 introduction.

**Effort**: Low (add a sentence).

**Recommend**: Yes — the shift between two cardinality notions within a single world should be explicitly acknowledged.

### 8. L08 and L09 are mechanically identical

**What**: L08 proves `∃ a b, a ≠ b ∧ f a = f b` for `f : Fin 5 → Fin 4` and L09 proves the same for `assign : Fin 6 → Fin 5`. The proofs are step-for-step identical: `apply Fintype.exists_ne_map_eq_of_card_lt` → `rw [Fintype.card_fin, Fintype.card_fin]` → `omega`.

**Why**: L09's stated purpose is "transfer moment: can you recognize pigeonhole in a word problem?" But the Lean statement is structurally identical to L08 — the only difference is the story wrapper. The learner who completed L08 can copy-paste the proof. For L09 to serve as a genuine transfer level, it should either (a) require a non-trivial modeling step (e.g., the learner must define the function themselves), or (b) use a different formalization that requires adapting the technique rather than repeating it.

**Where**: L09. Consider reformulating so the statement involves a different type structure (e.g., functions from a sum type, or a subtype constraint) that forces the learner to adapt rather than repeat.

**Effort**: Medium (redesign L09 statement).

**Recommend**: Consider — there is pedagogical value in repeated practice with minimal variation, but the repetition here is extreme. The boss (L10) already provides a variation (sum type domain), so L09's role is somewhat redundant. If kept as-is, at least reduce the hints to force the learner to recall the pattern independently.

### 9. Historical/motivational context for the pigeonhole principle is absent

**What**: No level mentions the history or broader significance of the pigeonhole principle. The name "pigeonhole" appears without explanation of its origin or its status as one of the most widely applied principles in combinatorics.

**Why**: A sentence or two about the Schubfachprinzip (Dirichlet's box principle, 1834) and one or two famous applications (e.g., "in any group of 367 people, two share a birthday") would make the principle feel significant rather than merely formal. The L06 introduction says "one of the most powerful and intuitive counting arguments in mathematics" but offers no evidence for this claim.

**Where**: L06 introduction (add 2-3 sentences of historical context and a famous application).

**Effort**: Low (text addition).

**Recommend**: Consider — the world is not sterile, but a touch of historical grounding would strengthen the motivational frame.

### 10. `simp` is disabled but its absence is never explained to the learner

**What**: The `DisabledTactic` line includes `simp` and `simp_all` across all levels, but no level explains why these tactics are disabled or what they would do if enabled.

**Why**: A learner who tries `simp` and gets an error message will be confused. A `TacticDoc` entry for `simp` (explaining that it is disabled in this world to ensure the learner works through cardinality rewrites manually) would prevent frustration. This is consistent with the project's established pattern of documenting disabled tactics.

**Where**: L01 (add `TacticDoc` for `simp` explaining the disable rationale).

**Effort**: Low (add a `TacticDoc` block).

**Recommend**: Yes — per the project's lessons learned, always add `TacticDoc` for disabled tactics.

## Overall impression

The world has a clear arc: three cardinality computation levels (sum, function, option), two proof-move setup levels (nonempty witness, contradiction via card), a three-level pigeonhole sequence (specific, general, collision), a transfer application, and a boss that integrates counting with pigeonhole. The writing is clean and the conclusions consistently provide plain-language translations, which is excellent. The progression from specific-case pigeonhole (L06) to general (L07) is good pedagogy.

The single most important improvement is **adding the missing subtype cardinality level** (suggestion 1). The plan explicitly calls for it, it covers a genuinely different facet of `Fintype` propagation, and its absence leaves an M14(S) coverage gap. The second priority is **redesigning L04** so that the `obtain` proof move cannot be bypassed by `exact h` — a level whose dominant lesson can be skipped by a one-word proof is not serving its purpose.
