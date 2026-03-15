# W12_ps CountingPset — Enrichment Review (Round 1)

**Reviewer**: enrichment-reviewer
**World**: CountingPset (W12_ps — Pset, 7 levels)
**Predecessor**: CountingPigeonhole (W12, 10 levels) + CountingFunctions (W12_ex, 5 levels)
**World promise**: The learner retrieves counting and pigeonhole skills under reduced scaffolding.

---

## Ranked Suggestions

### 1. L04 does not actually retrieve V8/V9 as planned — it retrieves only computation + omega

**What**: L04 ("Contradiction via cardinality") claims to retrieve V8 (nonemptiness argument) and V9 (contradiction via cardinality), but it does neither in its actual proof shape. The plan says "From cardinality > 0, extract a witness." The level instead gives `h : Fintype.card (Fin 3 + Bool) = 0` and asks the learner to compute `5 = 0` and close with `omega`. There is no witness extraction (V8) and no actual "cardinality zero implies emptiness" move (V9 as taught via `Finset.card_eq_zero` in W12 L05). The level is essentially another counting-computation level with `omega` at the end.

**Why**: This is the most important issue because the pset world's entire purpose is retrieval under fresh surface forms, and this level silently drops two of the seven retrieval targets (V8, V9). The learner never practices `obtain` on an existential, never uses `Finset.card_eq_zero` or its `Fintype` analogue, and never moves from "nonempty" to "witness." The title says "Contradiction via cardinality" but the proof is just `rw [...] at h; omega` — the same proof shape as L01-L03.

**Where**: L04, which needs a redesign. The level should present a genuine nonemptiness/emptiness argument. For example: given `h : Fintype.card (Fin 3 + Bool) > 0`, extract a term of type `Fin 3 + Bool` (retrieves V8). Or: given a hypothesis that a type is empty but also a term of that type, derive `False` using the emptiness (retrieves V9). The current formulation merely checks that `5 != 0`, which `omega` handles without any V8/V9 proof move.

**Effort**: Medium (rewrite the level statement and proof)

**Recommend**: Yes

---

### 2. Every non-transfer level has the same proof shape: `rw [...]; omega` or `apply ...; rw [...]; omega`

**What**: L01-L04 and L07 all follow the identical pattern: rewrite cardinalities, close with `omega`. Even the boss (L07) is this exact template with `apply Fintype.exists_ne_map_eq_of_card_lt` prepended. No level requires the learner to use `intro`, `obtain`, `exact`, `have`, or any proof structuring beyond rewriting and arithmetic.

**Why**: A pset world should test fluency, which means the learner should need to assemble proof steps in slightly different orders or combine skills that don't fit the same template. When every level is `rw/omega`, the learner is retrieving the *rewrite-then-omega* pattern rather than the individual proof moves. L03 is the closest to requiring a different proof shape (it uses `intro hsurj; have h := ...`) but even there, the reduced-scaffolding hint gives the entire strategy away.

**Where**: Consider making one level require a genuinely different proof shape. The redesigned L04 (suggestion #1) would help. Alternatively, the boss could require `have` subgoals, `obtain`, or a case split rather than a single `apply/rw/omega` chain.

**Effort**: Medium (restructuring one or two levels)

**Recommend**: Yes

---

### 3. L03 diverges from the plan: plan says "subset + cardinality to derive an inequality" (V15), but the level does reverse-pigeonhole (no-surjection)

**What**: The plan describes L03 as "Cardinality comparison: Use subset + cardinality to derive an inequality — Retrieval of V15." The actual level proves "no function `Fin 3 -> Fin 5` is surjective" using `Fintype.card_le_of_surjective`, which is exactly the same skill as W12_ex L03. The plan's V15 tag suggests a *subset cardinality comparison* (e.g., `|s| <= |t|` from `s ⊆ t`), which is a different proof move.

**Why**: This matters because the no-surjection argument was already drilled in W12_ex L03 with `Fin 2 -> Fin 3`. Doing it again with `Fin 3 -> Fin 5` changes only the numbers, not the proof shape. If V15 refers to a subset-cardinality inequality (as the plan suggests), the level should retrieve *that* skill rather than re-doing reverse pigeonhole. A level asking "given `s ⊆ t`, prove `s.card <= t.card`" or "use a cardinality inequality to show a set inclusion is strict" would be genuinely different retrieval.

**Where**: L03. Consider whether the level should be redesigned to match the plan's V15 retrieval target, or whether the current formulation is acceptable as a V15 variant.

**Effort**: Medium (rewrite the statement)

**Recommend**: Consider

---

### 4. Transfer levels (L05, L06) have near-zero proof difficulty — the transfer content is only in the conclusion text

**What**: L05 and L06 are labeled as transfer levels, but the Lean proof in each is trivially short (3 lines, same `apply/rw/omega` pattern). The "transfer" content — restating the proof in paper language — is entirely in the conclusion text that the learner reads passively. There is no mechanism to test whether the learner can actually perform the translation.

**Why**: This is inherent to the platform (lean4game has no free-text input), so it's not a defect per se. However, the levels currently feel like standard counting exercises with a paragraph glued on at the end, rather than genuine transfer practice. The introduction could at least frame the level as "write the paper proof first, then verify it in Lean," making the transfer an explicit cognitive step rather than an afterthought.

**Where**: L05 intro and L06 intro. Add a sentence like: "Before typing any Lean, write down the paper proof in your head (or on scratch paper). Then confirm it in Lean." This costs nothing and cues the transfer activity.

**Effort**: Low (a sentence in each introduction)

**Recommend**: Yes

---

### 5. The "Retrieval check" callouts in conclusions are metacognitive noise that may become invisible through repetition

**What**: Every conclusion contains a `**Retrieval check**:` callout that names the coverage item retrieved. This is good metacognitive scaffolding in principle, but when every single conclusion has one and they all follow the same template ("This level retrieved X (Vnn) on a fresh surface form"), the learner will stop reading them by L03.

**Why**: Varied phrasing or a different framing would keep these useful. For example, L01's retrieval check could ask a question ("Could you have done this without `Fintype.card_prod`? What if the type were `Fin 4 + Bool` instead?") rather than stating a fact. Even alternating between "Retrieval check" and "Reflection" or "Connection" would reduce the pattern-blindness effect.

**Where**: All conclusions. Vary the phrasing and occasionally make the retrieval check interrogative rather than declarative.

**Effort**: Low (rewrite 5-6 sentences across conclusions)

**Recommend**: Consider

---

### 6. L01 misses the opportunity to use a sum type (`Fin 4 + Bool`) alongside or instead of a product type

**What**: L01 uses `Fin 4 x Bool`, which retrieves `Fintype.card_prod`. The plan says the level should compute cardinality for "a type not seen before." However, sum types (`+`) were introduced in W12 L01, and a pset level using `Fin 4 + Bool` (retrieving `Fintype.card_sum`) would be a fresher surface form than another product. The learner has already seen `Fin 2 x Fin 3` (W11 L06), `Fin 2 x Bool` (W11 L08), and `Fin 3 x Fin 3` (L07 boss in this same world). Adding a sum-type variant would diversify the type constructors exercised.

**Where**: L01 or a potential additional level. Could either replace the current L01 (sum type instead of product) or be added as a second counting level (one product, one sum).

**Effort**: Low to medium (change the statement or add a level)

**Recommend**: Consider

---

### 7. The boss (L07) does not require "subset reasoning" as the plan promises

**What**: The plan says L07 should be "A proof combining counting, pigeonhole, and **subset reasoning**." The actual boss combines only counting and pigeonhole — there is no subset step, no `s ⊆ t` hypothesis, and no use of subset-related lemmas. The plan tags include V15 (G) which is a cardinality-comparison/subset move, but the proof doesn't use it.

**Why**: If V15 (G) is a genuine coverage target for the boss, the boss statement should require a subset or cardinality-comparison step alongside the pigeonhole step. For example, the boss could require first showing that a subset relationship holds (or that a cardinality inequality follows from a subset), and then feeding that into a pigeonhole argument. This would make the boss genuinely integrative rather than a slightly larger version of L02.

**Where**: L07. The statement would need restructuring to incorporate a subset step.

**Effort**: High (redesign the boss)

**Recommend**: Consider

---

### 8. No level uses `Fintype.card_option` — a compound-type constructor taught in W12 L03

**What**: W12 L03 taught `Fintype.card_option` (computing `Fintype.card (Option (Fin n))`) but the pset world never retrieves it. All compound types used are products (`x`), sums (`+`), or function spaces (`->`). An option type would be a fresh surface form that retrieves a less-drilled skill.

**Why**: The pset world should cover the breadth of type constructors taught in the lecture world. Products and functions are well-represented; option types are missing.

**Where**: Could replace L01 or be added as a variant. Example: `Fintype.card (Option (Fin 7)) = 8`.

**Effort**: Low (one statement change)

**Recommend**: Consider

---

## Overall Impression

The world delivers on its structural promise: 7 levels, reduced scaffolding (hints are hidden), fresh surface forms (different `Fin` sizes), transfer levels, and a boss. The conclusions are well-written with clear paper-proof parallels, and the world maintains the established disabled-tactic baseline. The coverage table in the boss conclusion is a strong metacognitive summary.

**The single most important improvement** is fixing L04 to actually retrieve the V8/V9 proof moves (witness extraction from nonemptiness, contradiction from emptiness) rather than being yet another `rw/omega` computation. As currently written, L04 is functionally identical to L01 in proof shape, and the world's claim to retrieve seven distinct skills is inflated to five-and-a-half. A redesigned L04 that requires `obtain` or `exact` to extract a witness, or that genuinely uses the emptiness-from-card-zero pattern, would make this world honest about its retrieval coverage and break the monotony of the `rw/omega` template.
