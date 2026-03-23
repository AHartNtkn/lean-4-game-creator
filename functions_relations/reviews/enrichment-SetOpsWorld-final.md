# Enrichment Review: SetOpsWorld

**Course**: functions_relations
**World**: SetOpsWorld (W03)
**Levels reviewed**: L01–L16

---

## Ranked Suggestions

### 1. Derive one De Morgan law from the other via double complement

**What**: Show that `(s ∩ t)ᶜ = sᶜ ∪ tᶜ` can be *derived* from `(s ∪ t)ᶜ = sᶜ ∩ tᶜ` plus `sᶜᶜ = s`, rather than proved independently from scratch.

**Why**: The world proves both De Morgan laws (L12, L13) and double complement (L15) as independent facts. But `(s ∩ t)ᶜ = (sᶜᶜ ∩ tᶜᶜ)ᶜ = ((sᶜ ∪ tᶜ)ᶜ)ᶜ⁻¹ ...` — more precisely, substitute `sᶜ` for `s` and `tᶜ` for `t` in the first De Morgan law, then apply double complement to both sides. This is a fundamentally different kind of mathematical reasoning: *composing results* rather than re-deriving from scratch. It demonstrates that the two De Morgan laws are not independent facts but consequences of a single law plus involution. This is the most important kind of mathematical depth the world is missing — the "why are there exactly two, and why do they look similar?" question.

**Where**: New level between L13 and L14 (or as an alternative proof path in L13's conclusion). Current L13 proves the dual De Morgan by brute force; an additional level could derive it from L12's result + `compl_compl`.

**Effort**: High (new level with a different proof structure)

**Recommend**: Yes — this is the single highest-impact improvement. It transforms the world from "here are many identities" to "here is a structure where identities generate each other."

---

### 2. Absorption laws: `s ∩ (s ∪ t) = s` and `s ∪ (s ∩ t) = s`

**What**: Add a level proving at least one absorption law.

**Why**: The world covers commutativity (L07, L10), De Morgan (L12, L13), complement laws (L09, L14), and distributivity (L16), but omits absorption — one of the most fundamental identities linking ∩ and ∪. Absorption is what makes {∪, ∩} a lattice rather than just two independent operations. It also has a genuinely different proof feel: the forward direction of `s ∩ (s ∪ t) = s` uses extraction (`.1`), while the backward direction builds both components from a single hypothesis (`exact ⟨hx, Or.inl hx⟩`). This is a natural exercise that uses familiar moves in a new configuration.

**Where**: New level between L08 and L09 (after both subset-of-union and intersection-subset are established).

**Effort**: High (new level)

**Recommend**: Yes — absorption is a structural identity on par with distributivity, and the proof is simple enough that it doesn't inflate world length disproportionately.

---

### 3. Dual distributivity as a derived result

**What**: Prove `s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u)` by composing De Morgan + distributivity + double complement, not by re-proving from scratch.

**Why**: L16's conclusion mentions the dual distributivity as a "challenge" but only suggests trying it "on paper." If the learner were to attempt it, they would likely repeat the same ext + constructor + cases proof from L16. But there is a slick derivation: complement both sides, apply De Morgan to convert unions to intersections (and vice versa), recognize the proven distributivity, then apply double complement. This teaches *proof composition* — using previously proven results as black boxes — which is the hallmark of mathematical maturity.

**Where**: New level after L16, or rework L16's conclusion to sketch the derivation. If the dual distributivity becomes a new level, the current L16 boss is still appropriate — the dual would be a "beyond the boss" victory lap.

**Effort**: High (new level) or medium (extended conclusion in L16)

**Recommend**: Consider — high impact but the world is already 16 levels. If absorption (suggestion 2) is added, this might push the world past a comfortable length. An extended conclusion in L16 that outlines the derivation could capture most of the value at lower cost.

---

### 4. `s ∩ sᶜ ⊆ ∅` vs `s ∩ sᶜ = ∅` — the subset-equality gap

**What**: In L09, briefly address (in the introduction or conclusion) why `ext` + `constructor` is needed rather than just proving `s ∩ sᶜ ⊆ ∅`, and connect this to the general pattern: a set equals `∅` iff it has no elements, which is logically `∀ x, x ∉ s` — a universal, not an existential.

**Why**: The conclusion explains the proof pattern mechanically but doesn't name the conceptual move: "To prove S = ∅, you prove S has no elements." This is a proof strategy that recurs throughout the course (empty preimage, empty intersection, etc.) and naming it here — at first use — would give the learner a reusable mental model. It is also the set-theoretic analogue of "to prove ∀, use intro" — a connection worth making explicit.

**Where**: L09 conclusion, 1-2 sentences.

**Effort**: Low (sentence in conclusion)

**Recommend**: Yes — naming a proof strategy at its point of introduction is high-value, low-cost.

---

### 5. Monotonicity of ∪ and ∩ under ⊆

**What**: Prove `s ⊆ t → s ∪ u ⊆ t ∪ u` or `s ⊆ t → s ∩ u ⊆ t ∩ u`.

**Why**: The world proves static subset facts (`s ∩ t ⊆ s`, `s ⊆ s ∪ t`) but never shows that operations *preserve* subset relationships. Monotonicity is a different flavor: it's about how a *relation between inputs* is inherited by the *outputs*. This foreshadows the image/preimage story (images preserve ⊆) and the lattice structure (⊔ and ⊓ are monotone). The proof combines the subset proof shape with case analysis on union (or extraction from intersection), exercising the full toolkit.

**Where**: New level between L10 and L11 (after case analysis is introduced).

**Effort**: High (new level)

**Recommend**: Consider — important conceptually but the world may be long enough. Could be deferred to a problem set world.

---

### 6. Naming the `change` + `push_neg` pattern explicitly

**What**: In L11's conclusion (or introduction), give this two-step pattern a name: "the complement unfolding pattern" or "the `change`-then-`push_neg` workflow."

**Why**: The pattern `change ¬(...) at hx` followed by `push_neg at hx` appears in L11, L12, L13, and L14. L11's conclusion says "Key workflow" but doesn't give it a memorable name. Naming recurring patterns helps learners recognize them. This is especially important because the need for `change` is a Lean-specific quirk (complement notation hides the negation from `push_neg`), and calling it out as a named workflow normalizes it rather than making it feel like a hack.

**Where**: L11 conclusion, 1-2 sentences.

**Effort**: Low (sentence in conclusion)

**Recommend**: Yes — naming a pattern at its point of introduction helps recognition in later levels.

---

### 7. Converse/partial converse of subset facts

**What**: After proving `s ∩ t ⊆ s` (L06) and `s ⊆ s ∪ t` (L08), briefly note in the conclusion: "Is the converse true? Is `s ⊆ s ∩ t` always true? No — that would mean `s ⊆ t`. So `s ∩ t ⊆ s` tells us intersection *only loses information*, and `s ⊆ s ∪ t` tells us union *only gains information*."

**Why**: The world proves one-way subset facts without asking whether the other direction holds. Flagging that the converse fails — and what its failure *means* — reinforces the asymmetry of ∩ (shrinks) vs ∪ (grows) and helps the learner build geometric intuition about these operations.

**Where**: L06 or L08 conclusion, 2-3 sentences.

**Effort**: Low (sentence in conclusion)

**Recommend**: Consider — nice pedagogical moment but minor.

---

### 8. The `contradiction` tactic as a named alternative

**What**: Formally introduce `contradiction` as a tactic that automatically closes goals when the context contains `h : P` and `h' : ¬P`.

**Why**: `contradiction` appears in Branch paths in L09, L12, and L13 but is never formally introduced. The world teaches the manual pattern `exact hns hs` for applying a negation. While the manual version is pedagogically correct for *first exposure*, by L12-L13 the learner has done it enough times that naming the automation would be appropriate. It also connects to the broader Lean philosophy: learn the manual move first, then learn the automation that handles it.

**Where**: L12 or L13 conclusion, or as a `NewTactic` in one of those levels with a brief note.

**Effort**: Low (add TacticDoc + NewTactic + sentence in conclusion)

**Recommend**: Consider — useful but the manual approach has pedagogical value, and introducing `contradiction` might encourage skipping the reasoning step.

---

## Overall Impression

SetOpsWorld is a well-structured world with strong pedagogy. The operation-to-logic correspondence table is built incrementally (L01-L04) and reinforced throughout. The progression from concrete membership proofs (L01-L04) to abstract identities (L05-L16) is natural. The De Morgan levels (L11-L13) and classical reasoning levels (L13-L15) are particularly well done — the constructive/classical asymmetry is explicitly addressed, which is rare and valuable.

The single most important improvement is **suggestion 1: showing that one De Morgan law derives from the other**. The world currently proves many identities but treats them as independent facts. Showing that results *generate each other* — that the two De Morgan laws are really one law plus an involution — would transform the world's mathematical message from "here are tools" to "here is structure." This is the kind of insight that, once pointed out, feels obviously important.
