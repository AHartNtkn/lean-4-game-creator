# Enrichment Review: W1 FinIntro ("What is Fin n?")

Reviewer: lean4game-enrichment-reviewer
Date: 2026-03-14
World files: L01_WhatIsFin through L08_Boss (8 levels)

---

## Ranked suggestions

### 1. Fin.succ is missing entirely -- the plan calls for it, the world omits it

**What**: The plan (W1, level 7) explicitly calls for a level on `Fin.succ` teaching that `(Fin.succ i).val = i.val + 1`. The world jumps from L06 (Coercion) to L07 (last/castSucc) to L08 (Boss), skipping `Fin.succ` entirely.

**Why**: `Fin.succ` is a fundamental navigation function in `Fin n`. It maps `Fin n` to `Fin (n + 1)` by incrementing the value, and it is the natural partner to `Fin.castSucc`. The plan's level 7 was designed to teach successor navigation as a separate concept before the boss level integrates everything. Without it, the world omits coverage item M2 (S) for `Fin.succ` and leaves the learner without a tool they will need repeatedly in W2 (computing with `Fin`) and W11+ (fintype/induction contexts where `Fin.succ` and `Fin.castSucc` partition `Fin (n+1)`). The conclusion of L07 already mentions the partition `Fin (n+1) = castSucc (Fin n) union {last n}`, but without having met `Fin.succ`, the learner does not understand the successor embedding that is dual to this partition.

**Where**: New level between current L07 and L08 (would become L08, pushing the boss to L09).

**Effort**: High (new level).

**Recommend**: Yes.

---

### 2. The castSucc/last partition deserves a proof level, not just a remark

**What**: L07's conclusion describes the partition `Fin (n+1) = castSucc '' (Fin n) union {last n}` in prose and ASCII art, but the learner never proves anything about `Fin.castSucc`. The level only asks for `(Fin.last 4).val = 4`, which is trivially `rfl`.

**Why**: The partition of `Fin (n+1)` into `castSucc` image and `last` is one of the most important structural facts about `Fin`. It is the basis for induction on `Fin`-indexed sums (W14), for defining functions by cases on `Fin (n+1)` (W2), and for the `Fin.lastCases` / `Fin.succAbove` API. A level that proves something about `castSucc` -- even just `(Fin.castSucc i).val = i.val` for a specific `i` -- would give the learner hands-on experience with the function rather than just reading about it in a conclusion. As it stands, `Fin.castSucc` appears in `NewDefinition` but is never used in a proof.

**Where**: Modify L07 to split into two levels: one for `Fin.last` (current statement) and one for `Fin.castSucc` (e.g., prove `(Fin.castSucc (2 : Fin 4)).val = 2` or prove `Fin.castSucc i != Fin.last n` for a given `i`). Alternatively, add one level after L07.

**Effort**: Medium (modify existing level + possibly add one).

**Recommend**: Yes.

---

### 3. L01 and L03 teach overlapping content with no deepening -- derivable fact left un-derived

**What**: L01 teaches `exact <3, by omega>` to build a `Fin 5`. L03 teaches that `<2, by omega> : Fin 5 = 2` via `rfl`. Both levels construct `Fin` elements with angle brackets. The connection -- that Lean's numeric literal `(k : Fin n)` is *defined as* `Fin.mk k proof` -- is stated in L03's prose but never tested as a proof obligation. Meanwhile, the deeper fact that `Fin.ext_iff` (two `Fin` elements are equal iff their values are equal) is mentioned in L03's introduction but never used in a proof until L05.

**Why**: L03 is a missed opportunity to teach `Fin.ext_iff` as a derivable fact. The level could ask the learner to prove `<2, h1> = <2, h2>` for two *different* proofs `h1 h2 : 2 < 5`, making the point that the proof component is irrelevant -- only the value matters. This is the subtype extensionality principle, which is foundational for all later `Fin` reasoning (and for `Finset` extensionality in W7). Instead, L03 proves something that is `rfl`, which teaches nothing the learner didn't already know from L01.

**Where**: Replace L03's statement with a proof that two `Fin.mk` terms with the same value but (notionally) different proof terms are equal. The current `rfl` proof could be retained as a hint, but the pedagogical payload should be `Fin.ext_iff` or `Fin.ext`.

**Effort**: Medium (rewrite one level).

**Recommend**: Yes.

---

### 4. No level teaches `Fin.val_mk` or the round-trip `Fin.mk (Fin.val i) (Fin.isLt)= i`

**What**: The world teaches `Fin.val` (L02) and `Fin.mk` (L01/L03) separately but never connects them. The round-trip `Fin.mk i.val i.isLt = i` (or equivalently `Fin.eta`) is a derivable fact that crystallizes the subtype structure.

**Why**: Understanding that `Fin.mk` and `Fin.val` are inverses is the key insight about subtypes. It says: "a `Fin n` element is *nothing more* than a natural number with a proof." This round-trip will be implicitly needed every time the learner destructs or reconstructs `Fin` elements. Without an explicit level, the learner may struggle in W2 when they need to build `Fin` elements from computed values.

**Where**: New level after L03, or fold into the revised L03 (see suggestion 3).

**Effort**: Medium (new level or modification of L03).

**Recommend**: Yes.

---

### 5. L04 (Fin 0) gives away the proof move -- a "what if?" level would be stronger

**What**: L04 tells the learner to use `exact h.elim0` and mentions `absurd h.isLt (Nat.not_lt_zero _)` as an alternative, but the learner only needs to type one tactic. The proof move "from impossible input, derive anything" is handed to them rather than discovered.

**Why**: The impossibility of `Fin 0` is one of the most memorable moments in the world. If the learner first sees `h : Fin 0` in their context and has to *reason* about why this is absurd (perhaps by extracting `h.isLt : h.val < 0` with `have`, then using `omega` or `exact absurd ...`), the lesson lands harder. The current single-hint approach (`exact h.elim0`) makes this a one-tactic level with no reasoning. A two-step approach -- first `have := h.isLt`, then `omega` -- would teach the learner the *structure* of an impossibility argument rather than a magic function name.

**Where**: Modify L04. Change the hint sequence: first hint suggests `have h_lt := h.isLt`, second hint suggests `omega`. Keep `exact h.elim0` as an alternative mentioned in the conclusion ("In practice, `Fin.elim0` packages this argument for you").

**Effort**: Medium (modify one level).

**Recommend**: Yes.

---

### 6. The boss level (L08) does not use `Fin.last`, `Fin.castSucc`, or `ext` -- it only tests `intro` + `have` + `omega`

**What**: The boss claims to integrate "M1--M3, V1, N8" but the actual proof is `intro i; have hi := i.isLt; omega`. This does not exercise `Fin.last`, `Fin.castSucc`, `ext`, or `Fin.elim0`. It is effectively a re-skin of L02 (extract `isLt`) with an `intro` in front.

**Why**: A boss level should require the learner to combine skills from across the world. The current boss tests only the proof pattern from L02 and L06. A stronger boss would require at least two distinct proof moves from the world -- for example, a goal involving `Fin.last` that requires `ext` to reduce to arithmetic, or a universally quantified statement over `Fin (n+1)` that requires case-splitting into `castSucc` and `last`. Even a modest improvement -- such as a goal with a hypothesis `i != Fin.last 3` that requires reasoning about `Fin.last` -- would test more of the world's content.

**Where**: Rewrite L08 to require at least `ext` or `Fin.last`/`Fin.castSucc` in addition to `omega`.

**Effort**: Medium (rewrite one level).

**Recommend**: Yes.

---

### 7. No concrete enumeration of `Fin n` for any specific `n >= 2`

**What**: The world works with `Fin 5`, `Fin 4`, `Fin 1`, and `Fin 0` but never asks the learner to list or reason about all elements of a small `Fin n`. The learner never sees `Fin 3 = {0, 1, 2}` as a concrete set they can enumerate.

**Why**: W2 will introduce `fin_cases` for exhaustive case analysis, and W3_ex is an entire example world about `Fin 3`. But the mental model "Fin n has exactly n elements, namely 0 through n-1" needs to be grounded before `fin_cases` is introduced. A level that asks the learner to construct all three elements of `Fin 3` (or prove that a given list covers them all) would provide this grounding. This would also give an early preview of the `decide` tactic or a manual case split, building a bridge to W2.

**Where**: New level after L05 (singleton) and before L06 (coercion), or as part of L05's extension. Something like: "Construct all elements of `Fin 3`" or "Prove that `(0 : Fin 3) != (1 : Fin 3)`."

**Effort**: High (new level).

**Recommend**: Consider. The W3_ex world handles this more thoroughly, so the question is whether W1 needs any concretization beyond boundary cases. Given that W1 is the learner's first encounter with `Fin`, some minimal concretization before the boss level would be valuable.

---

### 8. Transfer moment in the conclusion is too brief and not tested

**What**: L08's conclusion contains a transfer paragraph ("Let i be any natural number with i < 4...") but this is passive reading, not active production. The learner never writes or verbalizes the paper-proof analogue.

**Why**: The plan explicitly lists V18 (R) as a coverage item for the boss, meaning `have` should be reviewed as a proof-structuring tool, and the transfer moment should connect to paper proofs. The current transfer is a one-paragraph afterthought. For W1, which establishes the foundational concept, the transfer moment should be more deliberate. A separate concluding level (or a richer conclusion with a reflective question) would make the transfer active rather than passive.

**Where**: Extend L08's conclusion, or add a brief transfer-focused level after the boss (L09) that asks the learner to match Lean proof steps to paper-proof steps (even if the "proof" is just selecting from options in a comment).

**Effort**: Low (extend conclusion) to Medium (add level).

**Recommend**: Consider. The game engine may not support free-form transfer exercises, so an extended conclusion with explicit step-by-step transfer narration may be the practical ceiling.

---

### 9. `Fin.mk` is never formally introduced via `NewDefinition`

**What**: L01 introduces `Fin` via `NewDefinition Fin` and loads many tactics. L03 discusses `Fin.mk` extensively in its introduction but does not include `NewDefinition Fin.mk`. The learner sees the angle bracket syntax `<val, proof>` but never sees `Fin.mk` appear in the inventory.

**Why**: `Fin.mk` is a named constructor that the learner will encounter in goal states and mathlib lemma statements. If it never appears in the inventory, the learner may not recognize it when it shows up later. Adding `NewDefinition Fin.mk` to L03 (or L01) would make the constructor visible in the sidebar/inventory, which aids recognition in later worlds.

**Where**: Add `NewDefinition Fin.mk` to L03.

**Effort**: Low (one line change).

**Recommend**: Yes.

---

### 10. Cross-world foreshadowing: `Fin n` as an index for `Finset.range n`

**What**: The world's conclusion (L08) previews W2 (`fin_cases` and `decide`) but never mentions the deep connection between `Fin n` and `Finset.range n` that will be central to W9 and W13--W16 (big operators over `range`).

**Why**: A brief sentence in the world introduction (L01) or conclusion (L08) like "Later in this course, you will see that sums over `Finset.range n` are intimately connected to `Fin n` -- each element of `range n` corresponds to an element of `Fin n`" would seed the vocabulary and mental model for the big-operator worlds. This costs nothing and helps the learner see `Fin` as more than an abstract subtype exercise -- it is the indexing type for finite sums.

**Where**: L08 conclusion or L01 introduction.

**Effort**: Low (a sentence or two).

**Recommend**: Yes.

---

### 11. `Fin.ext` tactic is introduced in L05 but not connected to the `ext` principle

**What**: L05 uses `ext` to reduce `a = b` to `a.val = b.val` for elements of `Fin 1`. The tactic is introduced via `NewTactic ext`. But the introduction does not explain that `ext` is a general-purpose tactic for proving equality of structured types by extensionality -- it will reappear for `Finset` equality in W7 and for function equality later.

**Why**: If the learner understands `ext` only as "a trick for `Fin` equality," they will be surprised when it reappears in W7 for finsets. A sentence in L05's introduction or conclusion -- "The `ext` tactic works whenever two objects are equal if their components are equal. You will see it again for finset equality" -- builds the right mental model.

**Where**: L05 conclusion.

**Effort**: Low (one sentence).

**Recommend**: Yes.

---

### 12. No "wrong way" or misconception level for `Fin n` elements being `1..n`

**What**: The plan lists misconception C6 ("Fin n elements are 0..n-1, not 1..n") with coverage at W1. L06's conclusion warns about this in a single sentence. But there is no level that makes the learner confront this misconception.

**Why**: Off-by-one errors with `Fin` are among the most common mistakes in Lean finite-math code. A level where the learner must prove `(n-1 : Fin n) != n` (which is a type error) or prove that `Fin.last (n-1)` has value `n-1` (not `n`) would force the learner to internalize the zero-indexing. As it stands, the misconception is mentioned but never tested.

**Where**: Could be folded into L07 (which already covers `Fin.last`) or added as a separate level.

**Effort**: Medium (new level or modification of L07).

**Recommend**: Consider. The warning in L06's conclusion may suffice for now, and W2/W3_ex will give further practice. But an explicit misconception-confronting level is almost always higher-value than a prose warning.

---

## Overall impression

**What the world does well**: The world has a clean pedagogical arc from construction (L01) to extraction (L02) to boundary cases (L04-L05) to navigation (L07) to integration (L08). The introductions and conclusions are well-written, with genuine transfer moments and accurate descriptions of the math. The prose explains *why* things work, not just *how*. The boundary cases (Fin 0, Fin 1) are well-placed and clearly motivated. The ASCII art in L07 is an effective visual aid.

**The single most important improvement**: Add the missing `Fin.succ` level (suggestion 1) and strengthen L07 so that `Fin.castSucc` is actually used in a proof, not just mentioned in prose (suggestion 2). Together, these changes would ensure that the world's three navigation functions (`Fin.last`, `Fin.castSucc`, `Fin.succ`) are all exercised rather than just defined, and the boss level would have more material to integrate. The current world teaches the *data* of `Fin n` well (val, isLt, mk) but underserves the *navigation* of `Fin n`, which is what makes it useful in practice.
