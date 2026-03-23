# Course Plan: Functions & Relations

## 1. Course Promise

By the end of this course, the learner will be able to:
- Reason about sets as predicates, unfolding membership to propositional logic
- Prove set equalities by extensionality and derive subset relations
- Work with images, preimages, and their (a)symmetries under set operations
- Prove injectivity, surjectivity, and bijectivity using canonical proof shapes, both globally and on restricted sets
- Construct and verify equivalence relations, build quotient types, and lift functions through quotients
- State and use the partition–equivalence-relation correspondence
- Navigate subtypes, coercions, and the `↥s` notation connecting sets and types
- Build `Equiv` structures and reason about bundled bijections
- Prove countability via injections/encodings, prove uncountability via Cantor-style diagonalization
- Translate between formal Lean proofs and informal mathematical reasoning about functions, relations, and cardinality

## 2. Learner Profile

- **Prerequisites**: NNG4-level Lean fluency. The learner can use `rw`, `exact`, `apply`, `intro`, `cases`, `constructor`, `assumption`, `have`, `use`, and `induction`. They can read goal states and work in tactic mode.
- **What they do NOT know**: Sets as predicates (`Set α = α → Prop`); set-builder notation `{x | p x}`; image/preimage notation (`f '' s`, `f ⁻¹' t`); indexed unions/intersections; `ext` for set extensionality; `rintro`/`rcases`/`obtain` for pattern matching; `push_neg`; `Setoid`/`Quotient` machinery; subtypes (`{x // p x}`); coercions (`↥s`); `Equiv`; `Countable`/`Encodable`/`Denumerable`.
- **Mathematical background**: Comfortable with propositional logic and natural number arithmetic. Informal familiarity with sets, functions, and injective/surjective is helpful but not assumed.

## 3. Granularity Plan

### Macro (course)
The course has 8 phases, 28 worlds. Each phase builds on the previous and adds one major conceptual layer.

### Meso (world)
Each world covers one theorem family, one proof-move cluster, or one concrete object family. The world introduction states the world's center of gravity. The boss integrates the world's main moves.

### Micro (level)
Each level isolates one dominant lesson. The novelty budget is strict: at most one new burden per level (new math, new proof move, new Lean tactic, OR new notation). Everything else should be familiar enough to be automatic.

## 4. World Graph

---

### Phase 1: Sets and Logic (Worlds 1–5)

---

#### W01: SetWorld (Onboarding/Lecture)

**Type**: Onboarding + Lecture hybrid

**Promise**: By the end of this world, the learner will understand that `Set α = α → Prop`, be able to unfold set membership to its predicate definition, prove simple membership statements, and work with `Set.univ` and `∅`.

**Theorem families**:
- `Set α` as `α → Prop`
- `Set.mem` / `∈` — membership
- `setOf` — `{x | p x}` notation
- `Set.univ` and `Set.empty` / `∅`
- `Set.mem_setOf_eq` (conceptual, not as a simp lemma)

**Proof-move goals**:
- Unfold `x ∈ {y | p y}` to `p x`
- Prove membership by evaluating the predicate
- Prove `x ∈ Set.univ` and `x ∉ (∅ : Set α)`

**Inventory changes**:
- `NewDefinition Set Set.mem setOf Set.univ Set.empty`
- `TheoremTab "Set"`

**Level sketch**:
- L01: Welcome to sets. What is `Set α`? Trivial membership: prove `x ∈ (Set.univ : Set ℕ)`. Lesson: sets are predicates; membership is applying a predicate.
- L02: Set builder notation. Prove `3 ∈ {n : ℕ | n < 5}`. Lesson: `{x | p x}` notation unfolds to `p x`.
- L03: Non-membership. Prove `7 ∉ {n : ℕ | n < 5}`. Lesson: `∉` is `¬ ∈`.
- L04: An infinite set. Prove `4 ∈ {n : ℕ | Even n}`. Lesson: sets need not be finite.
- L05: The empty set. Prove `∀ n : ℕ, n ∉ (∅ : Set ℕ)`. Lesson: `∅` has no elements; `intro` then unfold.
- L06: Universal set. Prove `∀ n : ℕ, n ∈ Set.univ`. Lesson: everything is in `Set.univ`.
- L07 (Boss): Given `p : ℕ → Prop` and a hypothesis about `p`, prove membership and non-membership in `{n | p n}`. Integration of unfolding + logic.

**Misconceptions addressed**: Sets are not types; `x ∈ s` is a `Prop`.

**Dependencies**: None (first world)

**Pset partner**: PsetSets (W05)

---

#### W02: SubsetWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to prove subset relations using `intro x hx` and prove set equality using `ext x` (double containment).

**Theorem families**:
- `Set.subset` / `⊆` — `∀ x, x ∈ s → x ∈ t`
- `Set.ext` — `s = t ↔ ∀ x, x ∈ s ↔ x ∈ t`
- `∅ ⊆ s`, `s ⊆ Set.univ`
- Subset transitivity
- `Set.Subset.antisymm` — `s ⊆ t → t ⊆ s → s = t`

**Proof-move goals**:
- Prove `s ⊆ t` by `intro x hx` then derive `x ∈ t`
- Prove `s = t` by `ext x` then prove `↔`
- Chain subset relations for transitivity

**Inventory changes**:
- `NewTactic ext` — extensionality tactic
- `NewDefinition Set.Subset`
- `NewTheorem Set.Subset.antisymm`

**Level sketch**:
- L01: Prove `{n : ℕ | n < 3} ⊆ {n | n < 5}`. Lesson: `⊆` means `∀ x, x ∈ s → x ∈ t`; proof shape is `intro x hx`.
- L02: Prove `∅ ⊆ s` for any set `s`. Lesson: vacuous truth.
- L03: Prove `s ⊆ Set.univ`. Lesson: everything is in `univ`.
- L04: Subset transitivity. Given `s ⊆ t` and `t ⊆ u`, prove `s ⊆ u`. Lesson: chaining subset proofs.
- L05: Introduce `ext`. Prove `{n : ℕ | n < 3 ∧ n < 5} = {n | n < 3}`. Lesson: `ext x` reduces set equality to `∀ x, x ∈ s ↔ x ∈ t`, then `constructor` for `↔`.
- L06: Double containment without `ext`. Prove set equality from two subset hypotheses using `Set.Subset.antisymm`. Lesson: alternative route to set equality.
- L07 (Boss): Prove a set equality that requires both directions of double containment with nontrivial logic in each direction. Integration of `intro`, `ext`, `constructor`, subset chaining.

**Dependencies**: W01

**Pset partner**: PsetSets (W05)

---

#### W03: SetOpsWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand that set operations reduce to propositional logic: `∪` ↔ `∨`, `∩` ↔ `∧`, `ᶜ` ↔ `¬`, `\` ↔ `∧ ¬`.

**Theorem families**:
- `Set.union` / `∪` — connected to `∨`
- `Set.inter` / `∩` — connected to `∧`
- `Set.compl` / `ᶜ` — connected to `¬`
- `Set.diff` / `\` — connected to `∧ ¬`
- De Morgan's laws for sets

**Proof-move goals**:
- Unfold `x ∈ s ∪ t` to `x ∈ s ∨ x ∈ t` and use `left`/`right`
- Unfold `x ∈ s ∩ t` to `x ∈ s ∧ x ∈ t` and use `constructor`/`obtain`
- Unfold `x ∈ sᶜ` to `x ∉ s` (i.e., `¬ x ∈ s`)
- Use `push_neg` for complement and negation reasoning

**Inventory changes**:
- `NewTactic push_neg` — pushing negation through quantifiers
- `NewTactic left right` — disjunction introduction
- `NewDefinition Set.union Set.inter Set.compl Set.diff`

**Level sketch**:
- L01: Union membership. Prove `3 ∈ ({n | n < 5} ∪ {n | Even n})`. Lesson: `∪` means `∨`; use `left`.
- L02: Intersection membership. Prove `4 ∈ ({n | Even n} ∩ {n | n < 10})`. Lesson: `∩` means `∧`; use `constructor`.
- L03: Complement membership. Prove `3 ∈ {n : ℕ | Even n}ᶜ`. Lesson: `ᶜ` means `¬`; unfold and prove negation.
- L04: Set difference. Prove `3 ∈ ({n | n < 10} \ {n | Even n})`. Lesson: `\` means `∧ ¬`.
- L05: Introduce `push_neg`. Prove `x ∉ s ∩ t → x ∉ s ∨ x ∉ t`. Lesson: `push_neg` transforms negated conjunctions.
- L06: Subset with operations. Prove `s ∩ t ⊆ s`. Lesson: combining `intro`, membership unfolding, and `∧` elimination.
- L07: Subset with union. Prove `s ⊆ s ∪ t`. Lesson: `left` inside a subset proof.
- L08: De Morgan for sets. Prove `(s ∪ t)ᶜ = sᶜ ∩ tᶜ`. Lesson: `ext`, unfold operations, apply propositional De Morgan.
- L09 (Boss): Prove a distributivity law like `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`. Requires `ext`, both directions of `↔`, case analysis on `∨`, combining `∧`/`∨` moves.

**Misconceptions addressed**: Complement is not difference (`sᶜ = univ \ s`); `∉` is `¬ ∈`.

**Dependencies**: W01, W02

**Pset partner**: PsetSets (W05)

---

#### W04: IndexedOpsWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will work with indexed unions and intersections (`⋃ i, s i` and `⋂ i, s i`), cartesian products (`s ×ˢ t`), and `Set.Nonempty`.

**Center of gravity rationale**: This world bundles indexed operations, products, nonemptiness, and powerset because they all represent "compound set constructions beyond binary ∪/∩/ᶜ/\" — constructions that take families of sets, build products, or assert existence. The learner has just mastered binary operations in W03 and this world is the natural next layer of set-construction complexity. Splitting these into separate worlds would create worlds too small to sustain a coherent introduction-practice-boss arc.

**Theorem families**:
- `Set.iUnion` / `⋃ i, s i` — membership via `∃ i, x ∈ s i`
- `Set.iInter` / `⋂ i, s i` — membership via `∀ i, x ∈ s i`
- Bounded variants: `⋃ i ∈ t, s i` and `⋂ i ∈ t, s i`
- `Set.prod` / `s ×ˢ t` — membership is `∧`
- `Set.Nonempty` — `∃ x, x ∈ s`
- `Set.powerset` / `𝒫 s` — `𝒫 s = {t | t ⊆ s}`

**Proof-move goals**:
- Prove `x ∈ ⋃ i, s i` by `rw [Set.mem_iUnion]` then `use` witness index
- Prove `x ∈ ⋂ i, s i` by `rw [Set.mem_iInter]` then `intro i`
- Prove `Set.Nonempty s` by exhibiting a witness `⟨x, hx⟩`
- Prove `(a, b) ∈ s ×ˢ t` by proving `a ∈ s ∧ b ∈ t`

**Inventory changes**:
- `NewDefinition Set.iUnion Set.iInter Set.prod Set.Nonempty Set.powerset`
- `NewTheorem Set.mem_iUnion Set.mem_iInter`

**Level sketch**:
- L01: Indexed union. Prove membership in `⋃ k : Fin 3, {n : ℕ | n % 3 = k}`. Lesson: `⋃` means `∃`; `rw [Set.mem_iUnion]` then `use`.
- L02: Indexed intersection. Prove membership in `⋂ k : Fin 3, {n : ℕ | n ≥ k}`. Lesson: `⋂` means `∀`; `rw [Set.mem_iInter]` then `intro`.
- L03: Bounded indexed union. Work with `⋃ i ∈ Finset.range 3, ...`. Lesson: bounded variant unfolds to `∃ i, ∃ _ : i ∈ t, ...`.
- L04: Cartesian product. Prove `(2, 3) ∈ ({n | Even n} ×ˢ {n | n < 5})`. Lesson: `×ˢ` membership is `∧`.
- L05: Nonemptiness. Prove `Set.Nonempty {n : ℕ | Even n}`. Lesson: exhibit a witness.
- L06: Powerset. Prove `{n : ℕ | n < 3} ∈ 𝒫 {n | n < 5}`. Lesson: `𝒫` membership is `⊆`.
- L07: Indexed union equals univ. Prove `⋃ k : Fin 3, {n : ℕ | n % 3 = k} = Set.univ`. Lesson: `ext`, then both directions using `use`/`omega`.
- L08 (Boss): Prove a statement combining indexed operations with subset reasoning. E.g., `⋂ i, s i ⊆ s j` for a specific `j`. Requires `intro`, `mem_iInter`, specialization.

**Misconceptions addressed**: `⋃` uses `∃` (not `∨`); `⋂` uses `∀` (not `∧`); `×ˢ` is not `×`.

**Dependencies**: W01, W02, W03

**Pset partner**: PsetSets (W05)

---

#### W05: PsetSets (Problem Set)

**Type**: Pset

**Promise**: The learner retrieves and combines set-theory moves from W01–W04 on fresh surface forms with reduced scaffolding.

**Theorem families**: All from W01–W04, in new configurations.

**Proof-move goals**:
- Membership unfolding, subset proofs, set equality by `ext`, set operations to logic, indexed operations — all without prompting
- Transfer: state proof strategies in plain language

**Level sketch**:
- L01: Prove `{x : ℤ | x^2 = x} ⊆ {x | x = 0 ∨ x = 1}`. Fresh type (ℤ), requires membership unfolding + case analysis.
- L02: Prove `(s ∪ t) ∩ u ⊆ (s ∩ u) ∪ (t ∩ u)`. Abstract sets, no concrete type — pure logic transfer.
- L03: Prove `sᶜᶜ = s`. Double complementation via `ext` and `push_neg`.
- L04: Prove `s \ t = s ∩ tᶜ`. Connecting difference and complement.
- L05: Prove `⋃ i, {x | x = f i} = Set.range f`. Connecting indexed union to range (foreshadowing).
- L06: Prove a nonemptiness result about a cartesian product from nonemptiness of factors.
- L07 (Boss): Multi-step proof combining subset, extensionality, De Morgan, and indexed operations. E.g., prove that `(⋃ i, s i)ᶜ = ⋂ i, (s i)ᶜ` (De Morgan for indexed unions).

**Dependencies**: W01, W02, W03, W04

---

### Phase 2: Images and Preimages (Worlds 6–8)

---

#### W06: PreimageWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand preimages (`f ⁻¹' t`) and be comfortable with preimage membership, which reduces to simple function application.

**Theorem families**:
- `Set.preimage` / `f ⁻¹' t` — `x ∈ f ⁻¹' t ↔ f x ∈ t`
- Preimage preserves all set operations: `f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t`, etc.
- `f ⁻¹' Set.univ = Set.univ`, `f ⁻¹' ∅ = ∅`

**Proof-move goals**:
- Prove `x ∈ f ⁻¹' t` by showing `f x ∈ t` (direct computation)
- Prove preimage preserves intersection, union, complement

**Inventory changes**:
- `NewDefinition Set.preimage`
- `NewTheorem Set.mem_preimage`

**Level sketch**:
- L01: Preimage membership. Prove `3 ∈ (fun n : ℕ => n % 2) ⁻¹' {0}`. Lesson: `f ⁻¹' t` means `f x ∈ t`.
- L02: Preimage of empty set. Prove `f ⁻¹' ∅ = ∅`. Lesson: nothing maps into `∅`.
- L03: Preimage of univ. Prove `f ⁻¹' Set.univ = Set.univ`. Lesson: everything maps into `univ`.
- L04: Preimage preserves intersection. Prove `f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t`. Lesson: `ext`, unfold, the `∧` passes through.
- L05: Preimage preserves union. Prove `f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t`. Lesson: `∨` also passes through.
- L06: Preimage preserves complement. Prove `f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ`. Lesson: `¬` passes through.
- L07 (Boss): Prove `f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t`. Requires combining previous results or reproving from scratch using `ext` + membership unfolding.

**Dependencies**: W01, W02, W03

**Pset partner**: PsetImgPreimg (W08)

---

#### W07: ImageWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand images (`f '' s`), `Set.range`, and the critical asymmetry: image preserves unions but NOT intersections in general.

**Theorem families**:
- `Set.image` / `f '' s` — `y ∈ f '' s ↔ ∃ x ∈ s, f x = y`
- `Set.range` / `Set.range f` — image of `univ`
- Image preserves union: `f '' (s ∪ t) = f '' s ∪ f '' t`
- Image ONLY ⊆ for intersection: `f '' (s ∩ t) ⊆ f '' s ∩ f '' t`
- `image_subset_iff : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t` (Galois connection)

**Proof-move goals**:
- Prove `y ∈ f '' s` by exhibiting `⟨x, hx, rfl⟩`
- Prove `f '' s ⊆ t` by taking `y ∈ f '' s`, destructuring, then showing `y ∈ t`
- Use the Galois connection `image_subset_iff` to switch viewpoints

**Inventory changes**:
- `NewTactic obtain` — destructuring existentials
- `NewTactic rintro` — pattern-matching intro (intro with anonymous constructors)
- `NewTactic rcases` — deep pattern matching on hypotheses
- `NewDefinition Set.image Set.range`
- `NewTheorem Set.mem_image image_subset_iff`

**Level sketch**:
- L01: Image membership. Prove `6 ∈ (fun n => 2 * n) '' {0, 1, 2, 3}`. Lesson: exhibit a preimage witness `⟨x, hx, rfl⟩`.
- L02: Image of a predicate-defined set. Prove `y ∈ (fun n => 2 * n) '' {n | n < 5} → Even y`. Lesson: `obtain ⟨x, hx, hfx⟩` from image membership hypothesis.
- L03: `rintro` and `rcases`. Re-prove the L02 result using `rintro ⟨x, hx, rfl⟩` to destructure the image membership hypothesis in one step. Lesson: `rintro` combines `intro` and pattern matching; `rcases` does the same on existing hypotheses. These are the power tools for `∃`/`∧`/`∨` destructuring.
- L04: Image preserves union. Prove `f '' (s ∪ t) = f '' s ∪ f '' t`. Lesson: `ext`, both directions, using witnesses. Practice `rintro` for destructuring image membership.
- L05: Image only ⊆ for intersection. Prove `f '' (s ∩ t) ⊆ f '' s ∩ f '' t`. Lesson: the ⊆ direction; discuss why equality can fail.
- L06: `Set.range`. Prove `Set.range (fun n : ℕ => 2 * n) = {n | Even n}`. Lesson: `range f` = image of `univ`.
- L07: Galois connection. Use `image_subset_iff` to transform an image-subset goal into a preimage-subset goal. Lesson: switching viewpoints.
- L08: Image-preimage gap (⊆ direction). Prove `f '' (f ⁻¹' t) ⊆ t`. Lesson: this is only ⊆; equality requires surjectivity.
- L09: Preimage-image gap (⊇ direction). Prove `s ⊆ f ⁻¹' (f '' s)`. Lesson: this is only ⊇; equality requires injectivity.
- L10 (Boss): Prove that `f '' (f ⁻¹' t) = t` given that `f` is surjective onto `t` (i.e., `t ⊆ Set.range f`), and additionally prove `Set.Nonempty s → Set.Nonempty (f '' s)`. Requires combining image membership witnesses, preimage unfolding, surjectivity hypothesis, and nonemptiness transfer.

**Misconceptions addressed**: Image ≠ preimage for inclusions; image only preserves unions, not intersections.

**Dependencies**: W06, W01, W02, W03

**Pset partner**: PsetImgPreimg (W08)

---

#### W08: PsetImgPreimg (Problem Set)

**Type**: Pset

**Promise**: Transfer and retrieval for image/preimage moves on fresh problems.

**Level sketch**:
- L01: Prove `f '' ∅ = ∅` from scratch. No witnesses to exhibit.
- L02: Prove `f '' s ⊆ f '' t` from `s ⊆ t` (monotonicity of image).
- L03: Prove `f ⁻¹' (⋃ i, s i) = ⋃ i, f ⁻¹' (s i)`. Preimage distributes over indexed union.
- L04: Prove `f '' (⋂ i, s i) ⊆ ⋂ i, f '' (s i)`. Image only ⊆ for indexed intersection.
- L05: Concrete computation: compute `Nat.succ '' {0, 1, 2}` and `Nat.succ ⁻¹' {0}`. The preimage of `{0}` is `∅` (foreshadows: succ is injective but not surjective).
- L06 (Boss): Prove that `f ⁻¹' (f '' s) = s` given `Function.Injective f`. Requires injectivity hypothesis, image witness destructuring, and preimage unfolding.

**Dependencies**: W06, W07

---

### Phase 3: Functions — Injectivity, Surjectivity, Bijectivity (Worlds 9–12)

---

#### W09: InjectiveWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to prove injectivity using the canonical proof shape, compose and extract injectivity, and connect it to left inverses.

**Theorem families**:
- `Function.Injective` — `∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂`
- `Function.LeftInverse` — `g ∘ f = id`
- Left inverse → injective
- Composition preserves injectivity
- Injective (g ∘ f) → Injective f

**Proof-move goals**:
- Prove `Injective f` by `intro a b hab` then derive `a = b`
- Prove `Injective (g ∘ f)` from `Injective g` and `Injective f`
- Extract `Injective f` from `Injective (g ∘ f)`
- Construct a left inverse; use it to prove injectivity

**Inventory changes**:
- `NewDefinition Function.Injective Function.LeftInverse`
- `TheoremTab "Function"`

**Level sketch**:
- L01: Prove `Function.Injective (fun n : ℕ => n + 1)`. Lesson: the canonical shape: `intro a b hab`, then derive `a = b`.
- L02: Prove `Function.Injective (fun n : ℕ => 2 * n)`. Lesson: same shape, different algebra.
- L03: Non-injectivity. Prove `¬ Function.Injective (fun n : ℕ => n / 2)`. Lesson: provide a counterexample.
- L04: Composition. Given `Injective g` and `Injective f`, prove `Injective (g ∘ f)`. Lesson: unfold composition, apply both hypotheses.
- L05: Extraction. Given `Injective (g ∘ f)`, prove `Injective f`. Lesson: if `f a = f b` then `g (f a) = g (f b)` so `a = b`.
- L06: Left inverse. Given `g ∘ f = id`, prove `Injective f`. Lesson: apply `g` to both sides.
- L07 (Boss): Prove that `fun n : ℕ => 2 * n` is injective AND that `Injective (g ∘ f) → Injective f` using only `intro`/`apply`/algebra. Integration of direct proof + extraction.

**Dependencies**: W01

**Pset partner**: PsetFunctions (W12)

---

#### W10: SurjectiveWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to prove surjectivity by producing witnesses, compose and reason about surjectivity, and connect it to right inverses.

**Theorem families**:
- `Function.Surjective` — `∀ b, ∃ a, f a = b`
- `Function.RightInverse` — `f ∘ g = id`
- Right inverse → surjective
- Composition preserves surjectivity
- Surjective (g ∘ f) → Surjective g

**Proof-move goals**:
- Prove `Surjective f` by `intro b` then `use` a witness
- Compose surjectivity
- Extract `Surjective g` from `Surjective (g ∘ f)`
- Construct a right inverse

**Inventory changes**:
- `NewDefinition Function.Surjective Function.RightInverse`

**Level sketch**:
- L01: Prove `Function.Surjective (fun n : ℤ => n + 1)`. Lesson: `intro b`, `use b - 1`.
- L02: Non-surjectivity. Prove `¬ Function.Surjective (fun n : ℕ => 2 * n)`. Lesson: exhibit a `b` with no preimage (e.g., `b = 1`).
- L03: Surjective `fun n : ℕ => n / 2`. Lesson: witness construction for ℕ division.
- L04: Composition. Given `Surjective g` and `Surjective f`, prove `Surjective (g ∘ f)`. Lesson: chain witnesses.
- L05: Extraction. Given `Surjective (g ∘ f)`, prove `Surjective g`. Lesson: given `c`, get `a` with `g (f a) = c`, use `f a` as the witness for `g`.
- L06: Right inverse → surjective. Given `f ∘ g = id`, prove `Surjective f`. Lesson: `g b` is the witness.
- L07 (Boss): Multi-step problem requiring both witness production and extraction from composition. E.g., given `Surjective (g ∘ f)` and `Injective g`, prove `Surjective f`.

**Dependencies**: W09

**Pset partner**: PsetFunctions (W12)

---

#### W11: BijectiveWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will combine injectivity and surjectivity into bijectivity proofs, understand `Function.Bijective`, and see how inverses characterize bijections.

**Theorem families**:
- `Function.Bijective` — `Injective f ∧ Surjective f`
- Bijective from left + right inverse
- Composition of bijections
- `Function.bijective_iff_existsUnique` (conceptual)

**Proof-move goals**:
- Prove `Bijective f` by `constructor` then prove each half
- Use hypotheses about bijections to extract injective/surjective components
- Build two-sided inverses

**Inventory changes**:
- `NewDefinition Function.Bijective`

**Level sketch**:
- L01: Prove `Bijective (fun n : ℤ => n + 1)`. Lesson: `constructor`, then reuse injectivity and surjectivity proof shapes.
- L02: Prove `Bijective id`. Lesson: trivial case; reinforces the definition.
- L03: Extract. Given `Bijective f`, obtain `Injective f` and `Surjective f` separately and use them. Lesson: destructuring `∧`.
- L04: Composition. Given `Bijective g` and `Bijective f`, prove `Bijective (g ∘ f)`. Lesson: compose both components.
- L05: Inverse characterization. Given `g ∘ f = id` and `f ∘ g = id`, prove `Bijective f`. Lesson: left inverse gives injective, right inverse gives surjective.
- L06 (Boss): Prove a function is bijective by constructing its explicit two-sided inverse, verifying both `g ∘ f = id` and `f ∘ g = id`, and then concluding `Bijective f`. Integration of all function-property moves.

**Dependencies**: W09, W10

**Pset partner**: PsetFunctions (W12)

---

#### W12: PsetFunctions (Problem Set)

**Type**: Pset

**Promise**: Retrieval and transfer of injectivity/surjectivity/bijectivity on fresh problems.

**Level sketch**:
- L01: Prove `¬ Injective (fun _ : ℕ => (0 : ℕ))`. Constant function on ℕ (with `|ℕ| > 1`).
- L02: Prove `Injective f → Injective g → Injective (g ∘ f)` from scratch (no hints). Retrieval of composition.
- L03: Counterexample reasoning: `Injective (g ∘ f)` does NOT imply `Injective g`. Provide a counterexample (e.g., `f : Fin 1 → Fin 2`, `g : Fin 2 → Fin 2` with `g` non-injective but `g ∘ f` injective). (Alternatively: prove the positive direction `Injective (g ∘ f) → Injective f` as retrieval.)
- L04: Prove `Function.Surjective (fun n : ℕ => n / 2)` from scratch.
- L05: Given `LeftInverse g f` and `RightInverse g f`, prove `Bijective f`. Transfer: two-sided inverse ↔ bijection.
- L06 (Boss): Prove that composition of three bijections is bijective. Requires chaining composition twice.

**Dependencies**: W09, W10, W11

---

### Phase 4: Restricted Functions (Worlds 13–14)

---

#### W13: MapsToInjOnWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand function properties restricted to sets: `MapsTo`, `InjOn`, `SurjOn`, `BijOn`, and see why they differ from global properties.

**Theorem families**:
- `Set.MapsTo f s t` — `∀ x ∈ s, f x ∈ t`
- `Set.InjOn f s` — injectivity restricted to `s`
- `Set.SurjOn f s t` — surjectivity from `s` onto `t`
- `Set.BijOn f s t` — `MapsTo ∧ InjOn ∧ SurjOn`
- `Set.EqOn f g s` — equality on a set
- `InjOn f univ ↔ Injective f` — connection to global versions

**Proof-move goals**:
- Prove `MapsTo f s t` by `intro x hx` then show `f x ∈ t`
- Prove `InjOn f s` by `intro a ha b hb hab` then derive `a = b`
- Prove `SurjOn f s t` by `intro y hy` then produce `⟨x, hx, hfx⟩`
- Prove `BijOn f s t` by proving all three components

**Inventory changes**:
- `NewDefinition Set.MapsTo Set.InjOn Set.SurjOn Set.BijOn Set.EqOn`

**Level sketch**:
- L01: Prove `MapsTo (fun n => 2 * n) {n | n < 5} {n | n < 10}`. Lesson: `MapsTo` shape.
- L02: Prove `InjOn (fun n : ℕ => n % 3) {0, 1, 2}`. Lesson: `InjOn` shape — note this function is NOT globally injective.
- L03: Key example — `InjOn` without `Injective`. Prove `InjOn (fun n : ℕ => n^2) {n | 0 < n}` and show that `Injective (fun n : ℕ => n^2)` fails (since `(-2)^2 = 2^2` on ℤ, or on ℕ it's actually injective — use a different example). Alternative: `InjOn (fun n : ℕ => n % 5) {0, 1, 2, 3, 4}` vs not `Injective`.
- L04: Prove `SurjOn (fun n => 2 * n) {n | n < 5} {0, 2, 4, 6, 8}`. Lesson: `SurjOn` shape.
- L05: Prove `BijOn (fun n => 2 * n) {n | n < 5} {0, 2, 4, 6, 8}`. Lesson: combine `MapsTo`, `InjOn`, `SurjOn`.
- L06: Connection to global. Prove `InjOn f Set.univ ↔ Injective f`. Lesson: restricted to `univ` = global.
- L07 (Boss): Prove `BijOn` for a nontrivial function between two explicitly described sets, requiring all three components with real work in each. Integration of all on-set function property moves.

**Misconceptions addressed**: `InjOn f s` ≠ `Injective f`; `BijOn` needs `MapsTo` too, not just `InjOn ∧ SurjOn`.

**Dependencies**: W09, W10, W11, W07

---

#### W14: PsetRestricted (Problem Set)

**Type**: Pset

**Promise**: Retrieval and transfer for on-set function properties.

**Level sketch**:
- L01: Prove `MapsTo f s t → MapsTo f s (t ∪ u)`. Fresh surface form.
- L02: Prove `InjOn f s → s' ⊆ s → InjOn f s'`. Monotonicity of `InjOn`.
- L03: Prove `BijOn id s s`. Trivial but exercises the definition.
- L04: Prove `Set.LeftInvOn g f s` for a concrete pair. On-set inverse.
- L05 (Boss): Given `BijOn f s t` and `BijOn g t u`, prove `BijOn (g ∘ f) s u`. Composition of on-set bijections.

**Dependencies**: W13

---

### Phase 5: Relations, Equivalences, and Quotients (Worlds 15–20)

---

#### W15: RelationWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand binary relations as `α → α → Prop` and as `Set (α × α)`, check reflexivity/symmetry/transitivity, translate between both representations, and distinguish equivalence relations from non-equivalence relations.

**Theorem families**:
- Binary relation as `α → α → Prop`
- Binary relation as `Set (α × α)` — and translation between the two representations
- `Set.diagonal` — `{(x, x) | x}` as the equality relation in `Set (α × α)` form
- `Reflexive`, `Symmetric`, `Transitive` (unbundled)
- `Equivalence` — bundled refl+symm+trans

**Proof-move goals**:
- Check reflexivity: `intro x`, prove `R x x`
- Check symmetry: `intro x y hxy`, prove `R y x`
- Check transitivity: `intro x y z hxy hyz`, prove `R x z`
- Translate between `R : α → α → Prop` and `{p : α × α | R p.1 p.2} : Set (α × α)`
- Connect reflexivity to `Set.diagonal ⊆ {p | R p.1 p.2}`
- Bundle into `Equivalence` structure

**Inventory changes**:
- `NewDefinition Reflexive Symmetric Transitive Equivalence Set.diagonal`
- `TheoremTab "Relation"`

**Level sketch**:
- L01: Reflexivity. Prove `Reflexive (fun a b : ℕ => a % 3 = b % 3)`. Lesson: `intro x`, prove `R x x`.
- L02: Symmetry. Prove `Symmetric (fun a b : ℕ => a % 3 = b % 3)`. Lesson: `intro x y hxy`, use `hxy.symm` (or rewrite).
- L03: Transitivity. Prove `Transitive (fun a b : ℕ => a % 3 = b % 3)`. Lesson: `intro x y z hxy hyz`, chain equalities.
- L04: Not symmetric. Prove `¬ Symmetric (· ≤ · : ℕ → ℕ → Prop)`. Lesson: counterexample — `0 ≤ 1` but `¬ 1 ≤ 0`.
- L05: Not transitive. Prove a relation is not transitive. Lesson: counterexample.
- L06: Not reflexive. Prove `¬ Reflexive (· ≠ · : ℕ → ℕ → Prop)`. Lesson: counterexample — `0 ≠ 0` is false. Completes the three-property counterexample framework.
- L07: Relations as `Set (α × α)`. Given the mod-3 relation, restate it as `{p : ℕ × ℕ | p.1 % 3 = p.2 % 3}` and prove membership for a concrete pair. Introduce `Set.diagonal` as the equality relation: `Set.diagonal = {p | p.1 = p.2}`. Lesson: a relation is also a set of pairs.
- L08: Translation between representations. Prove that reflexivity of `R : α → α → Prop` is equivalent to `Set.diagonal ⊆ {p | R p.1 p.2}`. Lesson: the predicate and set-of-pairs views are interchangeable; `Set.diagonal` captures equality.
- L09: Bundle into `Equivalence`. Construct `Equivalence` for mod-3 from the three properties. Lesson: the `Equivalence.mk` constructor.
- L10: Same-parity equivalence. Prove `Equivalence (fun a b : ℕ => a % 2 = b % 2)`. Lesson: simplest nontrivial equivalence (2 classes). Practice the full 3-property workflow.
- L11 (Boss): Given a function `f : α → β`, prove that `fun a b => f a = f b` is an equivalence relation. This is the kernel equivalence — foreshadows `Setoid.ker`. Requires all three properties on an abstract function.

**Misconceptions addressed**: `≤` is not an equivalence relation; `≠` is not reflexive (and not transitive); relations can be viewed as predicates or as sets of pairs.

**Dependencies**: W01

**Pset partner**: PsetRelations (W18)

---

#### W16: SetoidWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand `Setoid α` as a bundled equivalence relation, construct `Quotient` types, and use `Quotient.mk'`, `Quotient.sound`, and `Quotient.exact`.

**Theorem families**:
- `Setoid α` — bundled equivalence relation as typeclass
- `Setoid.ker f` — kernel: `x ≈ y ↔ f x = f y`
- `Quotient` / `Quotient.mk'` — quotient type and projection
- `Quotient.sound` — `a ≈ b → ⟦a⟧ = ⟦b⟧`
- `Quotient.exact` — `⟦a⟧ = ⟦b⟧ → a ≈ b`

**Proof-move goals**:
- Construct a `Setoid` from an `Equivalence`
- Use `Quotient.mk'` to project into the quotient
- Prove `⟦a⟧ = ⟦b⟧` from `a ≈ b` using `Quotient.sound`
- Derive `a ≈ b` from `⟦a⟧ = ⟦b⟧` using `Quotient.exact`
- Use `≈` notation

**Inventory changes**:
- `NewDefinition Setoid Setoid.ker Quotient`
- `NewTheorem Quotient.sound Quotient.exact`

**Level sketch**:
- L01: Construct a `Setoid` on ℤ from the mod-3 equivalence relation. Lesson: `Setoid.mk` with an equivalence proof.
- L02: `Setoid.ker`. Given `f : ℤ → Fin 3` (the mod-3 projection), show that `Setoid.ker f` captures mod-3 equivalence. Lesson: kernel of a function is an equivalence relation.
- L03: `Quotient.mk'`. Form `⟦a⟧` for `a : ℤ` under the mod-3 setoid. Prove that `⟦0⟧ = ⟦3⟧`. Lesson: `Quotient.sound` from `0 ≈ 3`.
- L04: `Quotient.exact`. Given `⟦a⟧ = ⟦b⟧`, derive `a ≈ b`. Lesson: the reverse direction.
- L05: Prove `⟦a⟧ = ⟦b⟧ ↔ a ≈ b`. Lesson: `constructor`, then `Quotient.sound` and `Quotient.exact`.
- L06 (Boss): Given a function `f : α → β`, construct `Setoid.ker f`, form the quotient, and prove that two elements have the same quotient image iff they have the same `f`-value. Integration of setoid construction + quotient reasoning.

**Misconceptions addressed**: `≈` is not `=`; equivalence relation ≠ equality.

**Dependencies**: W15

**Pset partner**: PsetRelations (W18)

---

#### W17: QuotientLiftWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to lift functions through quotients using `Quotient.lift`, prove well-definedness obligations, and use `Quotient.inductionOn` for induction on quotient types.

**Theorem families**:
- `Quotient.lift` — lifting a function through a quotient
- Well-definedness: `a ≈ b → f a = f b`
- `Quotient.inductionOn` — induction on representatives
- `Quotient.map` — maps between quotient types

**Proof-move goals**:
- Define a function on a quotient via `Quotient.lift f h`
- Prove the well-definedness obligation `h : ∀ a b, a ≈ b → f a = f b`
- Use `Quotient.inductionOn` to prove properties of quotient elements

**Inventory changes**:
- `NewTheorem Quotient.lift Quotient.inductionOn Quotient.map`

**Level sketch**:
- L01: Simple lift. Lift a function `f : ℤ → ℕ` (e.g., `fun n => (n % 3).toNat`) through `Quotient (Setoid.ker f)`. The well-definedness is trivial (it follows from `ker` definition). Lesson: `Quotient.lift` mechanics.
- L02: Nontrivial well-definedness. Lift `fun n : ℤ => n^2 % 3` through the mod-3 quotient. Prove well-definedness: `a ≈ b → a^2 % 3 = b^2 % 3`. Lesson: the well-definedness proof is the real work.
- L03: Well-definedness failure. Show that `fun n : ℤ => n` does NOT respect the mod-3 equivalence (i.e., cannot be lifted). Lesson: not every function lifts.
- L04: `Quotient.inductionOn`. Prove a universal property about quotient elements by reducing to representatives. Lesson: induction on quotients.
- L05: `Quotient.map`. Given two setoids and a function that respects both, construct a map between quotients. Lesson: maps between quotient types.
- L06 (Boss): Given a surjective function `f : α → β`, lift a function `g : α → γ` through `Quotient (Setoid.ker f)`, prove well-definedness, and use `Quotient.inductionOn` to show a property of the lifted function. Integration of lift + well-definedness + induction.

**Misconceptions addressed**: Quotient lifting REQUIRES well-definedness proof; not every function can be lifted.

**Dependencies**: W16

**Pset partner**: PsetRelations (W18)

---

#### W18: PsetRelations (Problem Set)

**Type**: Pset

**Promise**: Retrieval and transfer for relations, setoids, and quotients.

**Level sketch**:
- L01: Prove same-parity on ℕ is an equivalence relation from scratch. Retrieval.
- L02: Construct the `Setoid` for "same last digit" on ℕ (mod 10). Fresh surface form.
- L03: Lift `fun n : ℕ => n % 2` through the same-parity quotient and prove well-definedness. Fresh example.
- L04: Prove that if `f : α → β` is injective, then `Setoid.ker f` is the trivial equivalence (equality). Transfer from injectivity to quotient theory.
- L05 (Boss): Given a new equivalence relation on ℤ × ℤ (e.g., `(a,b) ≈ (c,d) ↔ a + d = b + c` — constructing ℤ from ℕ × ℕ), construct the setoid, form the quotient, and lift addition through it with a well-definedness proof. Major integration exercise.

**Dependencies**: W15, W16, W17

---

#### W19: PartitionWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand partitions, prove the partition↔equivalence-relation correspondence, and work with equivalence classes.

**Theorem families**:
- `Setoid.classes` — the set of equivalence classes
- `Setoid.IsPartition` — partition conditions (no empty parts, covers the type, parts disjoint)
- Partition → equivalence relation
- Equivalence relation → partition
- The fundamental bijection

**Proof-move goals**:
- Prove a partition gives an equivalence relation
- Prove an equivalence relation gives a partition
- Work with equivalence classes as sets

**Inventory changes**:
- `NewDefinition Setoid.classes Setoid.IsPartition`

**Level sketch**:
- L01: Equivalence classes. For the mod-3 setoid, describe/prove a fact about the class of 0. Lesson: what an equivalence class looks like concretely.
- L02: Partition of ℤ into even/odd. Verify this is a partition. Lesson: the partition conditions.
- L03: Not a partition — overlapping parts. Show that `{{1,2}, {2,3}, {4}}` violates disjointness. Lesson: partition requires pairwise disjointness.
- L04: Not a partition — empty part. Show that including `∅` violates the no-empty-parts condition. Lesson: `IsPartition` excludes `∅`.
- L05: Partition → equivalence relation. Given a partition, define "same part" and show it's an equivalence relation. Lesson: the forward direction of the correspondence.
- L06: Equivalence relation → partition. Given an equivalence relation, show the equivalence classes form a partition. Lesson: the reverse direction.
- L07 (Boss): For the mod-3 equivalence on ℤ, prove that its equivalence classes form a partition AND that the partition recovers the original equivalence relation. Full round-trip of the correspondence.

**Misconceptions addressed**: Partitions have no empty parts; overlapping parts don't partition.

**Dependencies**: W15, W16

**Pset partner**: PsetRelations (W18) partially; also standalone review

---

#### W20: ThreeSamenessWorld (Example/Review)

**Type**: Example + Review

**Promise**: By the end of this world, the learner will explicitly distinguish the three notions of sameness: `=` (definitional equality), `≈` (equivalence under a relation), and `≃` (bijection with data).

**Theorem families**:
- Contrast `=`, `≈`, `≃` on concrete examples
- `Quotient.sound` / `Quotient.exact` revisited
- Foreshadowing: `Equiv` (to be built in Phase 6)

**Level sketch**:
- L01: `=` on ℕ. Two natural numbers are equal iff they are the same number. Trivial but sets the baseline.
- L02: `≈` on ℤ mod 3. `0 ≈ 3` but `0 ≠ 3`. Lesson: equivalence is coarser than equality.
- L03: From `≈` to `=` in the quotient. `0 ≈ 3` means `⟦0⟧ = ⟦3⟧` in the quotient. Lesson: the quotient makes `≈` into `=`.
- L04: Foreshadow `≃`. `Fin 2` and `Bool` are "the same" in what sense? Not `=` (different types). Not `≈` (no setoid between types). They are `≃` — there's a bijection with data. Conceptual level.
- L05 (Boss): Given a concrete situation, the learner must choose and use the correct notion of sameness for each sub-goal. Integration of all three notions.

**Dependencies**: W15, W16

**Transfer axis**: This is the key TRANSFER item — "Three notions of sameness" from the coverage map.

---

### Phase 6: Subtypes and Equivalences (Worlds 21–24)

---

#### W21: SubtypeWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will construct subtype elements, use coercions, navigate `↥s`, and distinguish `{x | p x}` (set) from `{x // p x}` (subtype/type).

**Theorem families**:
- `Subtype` — `{x : α // p x}`
- `Subtype.val` / `Subtype.coe` / coercion `(a : α)`
- `Subtype.mk` — constructing subtype elements
- `Subtype.ext` — equality of subtype elements
- `↥s` — coercion from `Set α` to `Type`

**Proof-move goals**:
- Construct `⟨x, proof⟩ : {x // p x}`
- Access value via `Subtype.val` or coercion
- Prove equality via `Subtype.ext`
- Navigate `↥s` coercion

**Inventory changes**:
- `NewDefinition Subtype Subtype.val Subtype.mk`
- `NewTheorem Subtype.ext Subtype.ext_iff`

**Level sketch**:
- L01: Construct `⟨3, proof⟩ : {n : ℕ // n > 0}`. Lesson: anonymous constructor for subtypes.
- L02: Access the value. Given `a : {n : ℕ // n > 0}`, prove a fact about `a.val`. Lesson: `Subtype.val` extracts the underlying element.
- L03: Coercion. Given `a : {n : ℕ // n > 0}`, prove a fact about `(a : ℕ)`. Lesson: coercion is `Subtype.val`.
- L04: Subtype equality. Prove that two subtype elements are equal by showing their values are equal. Lesson: `Subtype.ext`.
- L05: `↥s` coercion. Given `s : Set ℕ` and `a : ↥s`, prove a fact. Lesson: `↥s` turns a set into a type; elements have `.val` and `.property`.
- L06: Contrast `{x | p x}` and `{x // p x}`. Side-by-side: one is a `Set`, the other is a `Type`. Lesson: the fundamental notation distinction.
- L07: Restrict a function. Given `f : ℕ → ℕ` and `s : Set ℕ`, define `f` restricted to `↥s` → ℕ. Lesson: function restriction via subtypes.
- L08 (Boss): Given `s : Set ℕ` and a function `f : ↥s → ℕ`, construct a subtype element, apply `f`, and prove something about the result using both coercion and `Subtype.ext`. Integration.

**Misconceptions addressed**: `{x | p x}` is a `Set`, `{x // p x}` is a `Type`; `↥s` silently changes the type context.

**Dependencies**: W01, W02

---

#### W22: EquivWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will build `Equiv` structures from forward/inverse maps, compose and invert them, and understand `Equiv.ofBijective`.

**Theorem families**:
- `Equiv α β` — bundled equivalence `α ≃ β`
- `Equiv.toFun` / `Equiv.invFun`
- `Equiv.refl` / `Equiv.symm` / `Equiv.trans`
- `Equiv.ofBijective` — from `Bijective f` to `Equiv`
- `Equiv.ofInjective` — domain ≃ range for injective functions

**Proof-move goals**:
- Build `Equiv` by supplying `toFun`, `invFun`, `left_inv`, `right_inv`
- Compose with `Equiv.trans`
- Invert with `Equiv.symm`
- Construct from `Bijective` proof

**Inventory changes**:
- `NewDefinition Equiv Equiv.refl Equiv.symm Equiv.trans`
- `NewTheorem Equiv.ofBijective`
- `TheoremTab "Equiv"`

**Level sketch**:
- L01: `Equiv.refl`. Prove `ℕ ≃ ℕ` using `Equiv.refl`. Lesson: identity equivalence.
- L02: Build from scratch. Construct `Fin 2 ≃ Bool` by supplying `toFun`, `invFun`, `left_inv`, `right_inv`. Lesson: the four-field construction.
- L03: `Equiv.symm`. Given `e : α ≃ β`, produce `β ≃ α`. Lesson: inverting an equiv.
- L04: `Equiv.trans`. Given `e₁ : α ≃ β` and `e₂ : β ≃ γ`, produce `α ≃ γ`. Lesson: composing equivs.
- L05: `Equiv.ofBijective`. Given a `Bijective` function, produce an `Equiv`. Lesson: the bridge from predicates to data.
- L06: `Equiv.ofInjective`. Given `Injective f`, produce an equiv from the domain to the range. Lesson: domain ≃ range.
- L07 (Boss): Construct a nontrivial `Equiv` (e.g., between `{n : ℕ // n > 0}` and `ℕ` via `n ↦ n - 1` / `m ↦ m + 1`), prove both inverse conditions, then compose it with another equiv. Integration of construction + composition.

**Misconceptions addressed**: `Equiv` is data (forward + inverse + proofs), not just "bijectivity."

**Dependencies**: W09, W10, W11, W21

---

#### W23: PartialEquivWorld (Lecture — short)

**Type**: Lecture (short)

**Promise**: By the end of this world, the learner will understand `PartialEquiv` as a bijection between subsets, with explicit source and target.

**Theorem families**:
- `PartialEquiv α β` — local equivalences
- `PartialEquiv.source` / `PartialEquiv.target`
- `PartialEquiv.toFun` / `PartialEquiv.invFun`
- `PartialEquiv.symm`

**Proof-move goals**:
- Build a `PartialEquiv` with explicit source, target, forward, inverse, and proofs
- Use `PartialEquiv.symm`

**Inventory changes**:
- `NewDefinition PartialEquiv`

**Level sketch**:
- L01: Concrete example. Build a `PartialEquiv` between `ℕ` and `ℕ` with source `{n | n > 0}`, target `Set.univ`, forward `n ↦ n - 1`, inverse `m ↦ m + 1`. Lesson: what a local equivalence looks like.
- L02: Use the `PartialEquiv`. Given a `PartialEquiv`, prove something about its behavior on the source. Lesson: using the partial equiv's guarantees.
- L03: `PartialEquiv.symm`. Invert a partial equivalence and verify source/target swap. Lesson: symmetry of local equivalences.
- L04 (Boss): Build a `PartialEquiv` for a nontrivial example and verify a round-trip property. Integration.

**Dependencies**: W22

---

#### W24: PsetTypesEquiv (Problem Set)

**Type**: Pset

**Promise**: Retrieval and transfer for subtypes, equivs, and partial equivs.

**Level sketch**:
- L01: Construct an element of `↥{n : ℕ | Even n}` and extract its value. Retrieval.
- L02: Prove two elements of `{n : ℕ // n > 0}` are equal from a hypothesis about their values. `Subtype.ext` retrieval.
- L03: Build `Equiv` between `Bool` and `Fin 2` (reverse direction from W22). Fresh surface form.
- L04: Given `e : α ≃ β`, prove `Bijective e.toFun`. Transfer from `Equiv` back to `Bijective`.
- L05: Build `Equiv` from a composition of `Equiv.ofBijective` and `Equiv.trans`. Integration.
- L06 (Boss): Given a set `s` and a bijection `f` mapping `s` to `t`, construct an `Equiv` between `↥s` and `↥t`. Integration of subtypes + equivs + on-set bijections.

**Dependencies**: W21, W22, W23

---

### Phase 7: Countability and Cantor (Worlds 25–27)

---

#### W25: CountableWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will prove countability by constructing injections to ℕ, use `Encodable` for constructive countability, and close countability under standard operations.

**Theorem families**:
- `Countable α` — `∃ f : α → ℕ, Injective f`
- `Encodable α` — constructive countability with encode/decode
- `Denumerable α` — constructively bijective with ℕ
- `Set.Countable` — `Countable ↥s`
- Standard instances: ℕ, ℤ, ℚ
- Closure: products, sums, subtypes, quotients, images, subsets, countable unions

**Proof-move goals**:
- Prove countability by constructing an injection to ℕ
- Build an `Encodable` instance via encode/decode pair
- Transfer countability through images, subsets, unions
- Use `Denumerable.eqv` for `α ≃ ℕ`

**Inventory changes**:
- `NewDefinition Countable Encodable Denumerable Set.Countable`
- `NewTheorem Encodable.encode Encodable.decode`
- `TheoremTab "Count"`

**Level sketch**:
- L01: ℕ is countable. Prove `Countable ℕ` (trivially, using `id` as injection). Lesson: the definition.
- L02: ℤ is countable. Use the standard instance or construct an injection. Lesson: countability of a familiar type.
- L03: `Encodable`. Show how `Encodable ℕ` works with `encode`/`decode`. Lesson: the constructive interface.
- L04: `Denumerable`. Show `Denumerable ℕ` and `Denumerable.eqv` giving `ℕ ≃ ℕ`. Lesson: the strongest level — bijective with ℕ.
- L05: Product. Prove `Countable (ℕ × ℕ)`. Lesson: Cantor pairing (or just use the instance).
- L06: Subset. Prove `Set.Countable {n : ℕ | Even n}`. Lesson: countable subsets of countable types.
- L07: Image. Prove `Set.Countable (f '' s)` from `Set.Countable s`. Lesson: countability transfers through images.
- L08: Countable union. Prove a countable union of countable sets is countable. Lesson: the key closure property.
- L09 (Boss): Prove `Countable (ℕ × ℕ)` by explicit injection construction (not just using the instance), use `Denumerable.eqv` to obtain the explicit `ℕ ≃ ℕ × ℕ` equivalence (retrieval of Denumerable), then use closure to prove `Set.Countable` for a set defined by a compound predicate. Integration of construction + Denumerable retrieval + closure.

**Misconceptions addressed**: `Countable` is nonconstructive; `Encodable` is constructive; `Denumerable` requires surjectivity of decode.

**Dependencies**: W09, W21 (subtypes used for `Set.Countable`)

---

#### W26: CantorWorld (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand Cantor's theorem (no surjection `α → Set α`), prove it via the diagonal argument, and derive uncountability results.

**Theorem families**:
- `Function.cantor_surjective` — no surjection `α → Set α`
- `Function.cantor_injective` — no injection `Set α → α`
- Uncountability of `Set ℕ` / `ℕ → Bool`
- Cantor pairing (positive result: `ℕ × ℕ` is countable)

**Proof-move goals**:
- Diagonal argument: assume surjection, construct the diagonal set, derive contradiction
- Prove uncountability from Cantor's theorem
- Contrast with countable examples

**Inventory changes**:
- `NewTactic by_contra` — proof by contradiction (if not already available)
- `NewTheorem Function.cantor_surjective Function.cantor_injective`

**Level sketch**:
- L01: The diagonal set. Given `f : ℕ → Set ℕ`, define `S = {n | n ∉ f n}`. Lesson: the key construction.
- L02: The contradiction. Given `f : ℕ → Set ℕ` surjective and `S = {n | n ∉ f n}`, derive `n ∈ S ↔ n ∉ S`. Lesson: the paradox.
- L03: Cantor's theorem (surjective version). Prove `¬ Surjective (f : α → Set α)`. Lesson: full diagonal argument.
- L04: Cantor's theorem (injective version). Prove `¬ Injective (f : Set α → α)`. Lesson: dual version.
- L05: Uncountability of `Set ℕ`. Use Cantor to prove `¬ Countable (Set ℕ)`. Lesson: connecting Cantor to countability.
- L06: Contrast. Recall `Countable (ℕ × ℕ)`. Lesson: countable ≠ uncountable; products stay countable.
- L07 (Boss): Prove uncountability of `ℕ → Bool` (binary sequences) via a self-contained diagonal argument. Full integration: assume surjection from ℕ, construct diagonal, derive contradiction.

**Misconceptions addressed**: Cantor ≠ uncountability of ℝ (related but distinct); the diagonal argument works for any type, not just ℕ.

**Dependencies**: W09, W10, W25

---

#### W27: PsetCountability (Problem Set)

**Type**: Pset

**Promise**: Retrieval and transfer for countability and Cantor.

**Level sketch**:
- L01: Prove `Countable ℚ` (or use instance + prove a countable-set result involving ℚ). Fresh type.
- L02: Prove that a countable union of countable sets is countable, using closure. Retrieval.
- L03: Denumerable retrieval. Prove `Denumerable ℤ` (or use the instance), then use `Denumerable.eqv` to obtain the explicit `ℤ ≃ ℕ` equivalence and verify a round-trip property. Retrieval of Denumerable on a fresh type.
- L04: Encodable transfer. Construct an `Encodable` instance for a fresh type (e.g., `Option ℕ` or a sum type) by supplying explicit `encode`/`decode` functions. Transfer of the constructive countability interface to a new setting.
- L05: Prove `¬ Countable (ℕ → ℕ)`. Transfer: Cantor argument on a different type.
- L06: Prove `Set.Countable s → Set.Countable (f '' s)`. Retrieval of image + countability.
- L07 (Boss): Given a specific function `f : ℕ → Set ℕ`, exhibit a set not in its range by diagonal construction. Then prove `¬ Surjective f`. Transfer of Cantor to a concrete instance.

**Dependencies**: W25, W26

---

### Phase 8: Capstone (World 28)

---

#### W28: Finale (Review/Boss)

**Type**: Review + Capstone

**Promise**: By the end of this world, the learner will integrate all major course themes: sets, functions, relations, quotients, subtypes, equivs, and countability.

**Level sketch**:
- L01: First isomorphism theorem, concrete. For `f : ℤ → ZMod 3`, construct `Setoid.ker f`, form the quotient, and use `quotientKerEquivRange` to get the equiv. Integration of functions + quotients + equivs.
- L02: From surjection to equiv. Given surjective `f : α → β`, use `quotientKerEquivOfSurjective` to get `Quotient (ker f) ≃ β`. Integration.
- L03: Image and injectivity on sets. Prove `InjOn f s → f '' (s ∩ t) = f '' s ∩ f '' t`. Requires on-set injectivity + image reasoning.
- L04: Cantor meets sets. Prove `¬ ∃ f : Set ℕ → ℕ, Injective f`. Connects Cantor to function properties.
- L05: Subtype equiv via bijection on sets. Given `BijOn f s t`, construct `↥s ≃ ↥t`. The grand bridge: sets, on-set functions, subtypes, equivs — all in one proof.
- L06 (Final Boss): Prove that `Quotient.classes` of a setoid forms a partition (covering + disjoint + no empty parts), and conversely exhibit the setoid from a given partition. The round-trip of the fundamental theorem. Integration of all major themes.

**Dependencies**: All previous worlds

---

## 5. Coverage Closure Table

Each core item from the coverage map is mapped to its five coverage stages (I=introduction, S=supported practice, R=retrieval, G=integration/boss, T=transfer).

### Sets

| Item | I | S | R | G | T |
|------|---|---|---|---|---|
| `Set α` as predicate | W01 | W01 | W05 | W03 boss | W05 |
| `∈` / membership | W01 | W02, W03 | W05 | all bosses | W05, W08 |
| `⊆` / subset | W02 | W02, W03 | W05 | W03 boss | W05, W14 |
| `∅` and `Set.univ` | W01 | W02, W06 | W05 | W06 boss | W08 |
| `setOf` / `{x \| p x}` | W01 | W01, W03 | W05 | W03 boss | W05 |
| `∪`, `∩` | W03 | W03 | W05 | W03 boss | W05, W14 |
| `ᶜ`, `\` | W03 | W03 | W05 | W03 boss | W05 |
| `Set.prod` / `×ˢ` | W04 | W04 | W05 | W04 boss | W18 |
| `Set.powerset` | W04 | W04 | W05 | — | — |
| `Set.image` / `f '' s` | W07 | W07 | W08 | W07 boss | W08, W28 |
| `Set.preimage` / `f ⁻¹' t` | W06 | W06 | W08 | W06 boss, W07 boss | W08, W28 |
| `Set.range` | W07 | W07 | W08 | W28 | W27 |
| Image/preimage Galois connection | W07 | W07 | W08 | W07 boss | W28 |
| `⋃ i, s i`, `⋂ i, s i` | W04 | W04 | W05 | W04 boss, W05 boss | W08, W27 |
| Bounded `iUnion₂`/`iInter₂` | W04 | W04 | W05 | — | W08 |
| `Set.Nonempty` | W04 | W04, W07 | W05 | W07 boss | W07 boss |
| `Set.diagonal` | W15 | W15 | W18 | W15 boss | — |

### Functions

| Item | I | S | R | G | T |
|------|---|---|---|---|---|
| `Function.Injective` | W09 | W09 | W12 | W09 boss | W12, W28 |
| `Function.Surjective` | W10 | W10 | W12 | W10 boss | W12, W28 |
| `Function.Bijective` | W11 | W11 | W12 | W11 boss | W12, W24 |
| `Function.LeftInverse` | W09 | W09 | W12 | W11 | W12 |
| `Function.RightInverse` | W10 | W10 | W12 | W11 | W12 |
| Compose injectivity/surjectivity | W09, W10 | W09, W10 | W12 | W12 boss | W14 |
| Extract from composition | W09, W10 | W09, W10 | W12 | W10 boss | W12 |
| `Set.MapsTo` | W13 | W13 | W14 | W13 boss | W14, W28 |
| `Set.InjOn` | W13 | W13 | W14 | W13 boss | W14, W28 |
| `Set.SurjOn` | W13 | W13 | W14 | W13 boss | W14 |
| `Set.BijOn` | W13 | W13 | W14 | W13 boss | W14, W28 |
| `Set.EqOn` | W13 | W13 | W14 | — | — |
| Cantor's theorem (surjective) | W26 | W26 | W27 | W26 boss | W27, W28 |
| Cantor's theorem (injective) | W26 | W26 | W27 | W28 | W27 |

### Relations and Equivalences

| Item | I | S | R | G | T |
|------|---|---|---|---|---|
| Binary relation (`α → α → Prop` and `Set (α × α)`) | W15 | W15 | W18 | W15 boss | W18 |
| Reflexive / Symmetric / Transitive | W15 | W15 | W18 | W15 boss | W18 |
| `Equivalence` (bundled) | W15 | W15, W16 | W18 | W15 boss | W18 |
| `Setoid α` | W16 | W16, W17 | W18 | W16 boss | W18 |
| `Setoid.ker f` | W16 | W16, W17 | W18 | W17, W28 | W18 |
| `Quotient` / `Quotient.mk'` | W16 | W16, W17 | W18 | W16 boss, W17 boss | W18, W28 |
| `Quotient.sound` / `Quotient.exact` | W16 | W16, W20 | W18 | W16 boss | W18, W20 |
| `Quotient.lift` + well-definedness | W17 | W17 | W18 | W17 boss | W18 |
| `Quotient.inductionOn` | W17 | W17 | W18 | W17 boss | W28 |
| `Quotient.map` | W17 | W17 | — | — | — |
| Equivalence classes / `Setoid.classes` | W19 | W19 | W28 | W19 boss | W28 |
| `Setoid.IsPartition` | W19 | W19 | W28 | W19 boss | W28 |
| Partition–equivalence bijection | W19 | W19 | W28 | W19 boss, W28 boss | W28 |
| First isomorphism theorem | W28 | W28 | W28 boss | W28 | W28 |

### Types and Encodability

| Item | I | S | R | G | T |
|------|---|---|---|---|---|
| `Subtype` / `{x // p x}` | W21 | W21 | W24 | W21 boss | W24, W28 |
| `↥s` coercion | W21 | W21 | W24 | W21 boss, W28 | W24 |
| `Subtype.val` / `Subtype.coe` | W21 | W21 | W24 | W21 boss | W24 |
| `Subtype.mk` | W21 | W21 | W24 | W21 boss | W24 |
| `Equiv α β` | W22 | W22 | W24 | W22 boss | W24, W28 |
| `Equiv.refl` / `symm` / `trans` | W22 | W22 | W24 | W22 boss | W24, W28 |
| `Equiv.ofBijective` | W22 | W22 | W24 | W24 boss | W28 |
| `PartialEquiv` | W23 | W23 | W24 | W23 boss | — |
| `Countable α` | W25 | W25 | W27 | W25 boss | W27 |
| `Encodable α` | W25 | W25 | W27 | W25 boss | W27 |
| `Denumerable α` | W25 | W25 | W27 | W25 boss | W27 |
| `Set.Countable` | W25 | W25 | W27 | W25 boss | W27 |
| Countability closure (products, images, subsets, unions) | W25 | W25 | W27 | W25 boss | W27 |
| Uncountability via diagonal | W26 | W26 | W27 | W26 boss | W27, W28 |

### Proof Moves

| Move | I | S | R | G | T |
|------|---|---|---|---|---|
| Unfold set membership | W01 | W01-W04 | W05 | all bosses | W05, W08 |
| Prove subset by `intro x hx` | W02 | W02, W03 | W05 | W03 boss | W05, W14 |
| Set equality by `ext x` | W02 | W02, W03 | W05 | W03 boss | W05, W08 |
| Nonemptiness by witness | W04 | W04 | W05 | W07 boss | W05, W07 boss |
| Image membership by witness | W07 | W07 | W08 | W07 boss | W08, W28 |
| Preimage membership by application | W06 | W06 | W08 | W06 boss | W08 |
| Injectivity proof shape | W09 | W09 | W12 | W09 boss | W12, W13 |
| Surjectivity proof shape | W10 | W10 | W12 | W10 boss | W12, W13 |
| Compose/extract inj/surj | W09, W10 | W09, W10 | W12 | W12 boss | W14 |
| Left/right inverse construction | W09, W10 | W11 | W12 | W11 boss | W12 |
| Check refl/symm/trans | W15 | W15 | W18 | W15 boss | W18 |
| Quotient lift + well-definedness | W17 | W17 | W18 | W17 boss | W18 |
| Subtype construction + coercion | W21 | W21 | W24 | W21 boss | W24, W28 |
| Build `Equiv` from 4 fields | W22 | W22 | W24 | W22 boss | W24, W28 |
| Diagonal argument | W26 | W26 | W27 | W26 boss | W27, W28 |
| Partition ↔ equivalence proof | W19 | W19 | W28 | W19 boss | W28 |

## 6. Inventory Release Plan

### Tactics

| Tactic | World | Why now? | Taught or needed? | Visible? | Doc? |
|--------|-------|---------|-------------------|---------|------|
| `ext` | W02 | Set equality is the primary proof technique | Taught | Yes | `TacticDoc ext` — extensionality for sets |
| `push_neg` | W03 | Complement requires negation manipulation | Taught | Yes | `TacticDoc push_neg` — push negation through quantifiers |
| `left` / `right` | W03 | Union membership requires disjunction | Taught | Yes | `TacticDoc left`, `TacticDoc right` |
| `obtain` | W07 | Image membership requires destructuring existentials | Taught | Yes | `TacticDoc obtain` — destructure hypotheses |
| `by_contra` | W26 | Cantor's theorem requires contradiction | Taught | Yes | `TacticDoc by_contra` — proof by contradiction |
| `rintro` | W07 | Pattern-matching intro for image/existential destructuring | Taught | Yes | `TacticDoc rintro` — intro with anonymous constructors |
| `rcases` | W07 | Deep pattern matching on hypotheses | Taught | Yes | `TacticDoc rcases` — destructure hypotheses with patterns |

### Disabled tactics (baseline, all worlds)
`trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all`

### Per-world disabling

| World(s) | Additional disabled | Reason |
|----------|-------------------|--------|
| W01–W05 | `tauto` | Must learn set-logic connection manually |
| W01–W05 | `omega` (on concrete ℕ levels) | Must not bypass set reasoning with arithmetic |
| W02 L01–L04 | `ext` | Must learn subset shape before `ext` shortcut |
| W06–W08 | `tauto` | Must unfold image/preimage manually |
| W09–W12 | `Function.Injective.comp`, `Function.Surjective.comp`, `Function.Bijective.comp` | Must compose manually |
| W15–W18 | `tauto` | Must check relation properties manually |
| W16–W17 | `Quotient.eq` | Must use `sound`/`exact` manually |
| All set-equality levels | Lattice aliases (see coverage map §6) | Prevent `exact sup_comm` etc. |
| All set-equality levels | `Set.union_comm`, `Set.inter_comm`, etc. | Prevent one-line closers |

### Definitions/Theorems Release

| Item | World | Why now? | Tab |
|------|-------|---------|-----|
| `Set`, `Set.mem`, `setOf`, `Set.univ`, `Set.empty` | W01 | Foundation | Set |
| `Set.Subset`, `Set.Subset.antisymm` | W02 | Subset reasoning | Set |
| `Set.union`, `Set.inter`, `Set.compl`, `Set.diff` | W03 | Set operations | Set |
| `Set.iUnion`, `Set.iInter`, `Set.prod`, `Set.Nonempty`, `Set.powerset` | W04 | Indexed ops | Set |
| `Set.preimage`, `Set.mem_preimage` | W06 | Preimage | Set |
| `Set.image`, `Set.range`, `Set.mem_image`, `image_subset_iff` | W07 | Image | Set |
| `Function.Injective`, `Function.LeftInverse` | W09 | Injectivity | Function |
| `Function.Surjective`, `Function.RightInverse` | W10 | Surjectivity | Function |
| `Function.Bijective` | W11 | Bijectivity | Function |
| `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`, `Set.EqOn` | W13 | Restricted functions | Function |
| `Reflexive`, `Symmetric`, `Transitive`, `Equivalence` | W15 | Relations | Relation |
| `Setoid`, `Setoid.ker`, `Quotient`, `Quotient.sound`, `Quotient.exact` | W16 | Setoid/quotient | Relation |
| `Quotient.lift`, `Quotient.inductionOn`, `Quotient.map`, `Setoid.quotientKerEquivRange` | W17 | Quotient lifting | Relation |
| `Setoid.classes`, `Setoid.IsPartition` | W19 | Partitions | Relation |
| `Subtype`, `Subtype.val`, `Subtype.mk`, `Subtype.ext` | W21 | Subtypes | Type |
| `Equiv`, `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, `Equiv.ofBijective` | W22 | Equivs | Equiv |
| `PartialEquiv` | W23 | Local equivs | Equiv |
| `Countable`, `Encodable`, `Denumerable`, `Set.Countable` | W25 | Countability | Count |
| `Function.cantor_surjective`, `Function.cantor_injective` | W26 | Cantor | Count |

## 7. Boss Map

| World | Boss description | Subskills integrated | Source levels |
|-------|-----------------|---------------------|---------------|
| W01 boss | Membership/non-membership from predicate hypothesis | Unfold membership, evaluate predicate, prove/disprove | W01 L01–L06 |
| W02 boss | Set equality requiring nontrivial double containment | `ext`, `intro`, `constructor`, subset chaining | W02 L01–L06 |
| W03 boss | Distributivity law `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)` | `ext`, `↔`, case analysis on `∨`, combining `∧`/`∨` | W03 L01–L08 |
| W04 boss | `⋂ i, s i ⊆ s j` with indexed operations | `intro`, `mem_iInter`, specialization | W04 L01–L07 |
| W05 boss | De Morgan for indexed unions | `ext`, `push_neg`, `mem_iUnion`, `mem_iInter`, complement | W01–W04 all |
| W06 boss | `f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t` | Preimage + difference + ext | W06 L01–L06 |
| W07 boss | `f '' (f ⁻¹' t) = t` given surjectivity condition | Image witness, preimage unfold, surjectivity use | W06–W07 all |
| W08 boss | `f ⁻¹' (f '' s) = s` given injectivity | Injectivity + image witness + preimage | W06–W07 all |
| W09 boss | Direct injectivity proof + extraction from composition | `intro a b hab`, algebra, composition reasoning | W09 L01–L06 |
| W10 boss | `Surjective (g ∘ f)` + `Injective g` → `Surjective f` | Witness production, extraction, combining hypotheses | W09–W10 |
| W11 boss | Bijection from two-sided inverse | Left inv → inj, right inv → surj, combine | W09–W11 |
| W12 boss | Composition of three bijections | Chaining composition twice | W09–W11 all |
| W13 boss | `BijOn f s t` for nontrivial sets | `MapsTo` + `InjOn` + `SurjOn` all with real work | W13 L01–L06 |
| W14 boss | Composition of `BijOn` | On-set composition of all three components | W13–W14 |
| W15 boss | Kernel equivalence: `fun a b => f a = f b` is an equivalence | Refl + symm + trans on abstract function | W15 L01–L07 |
| W16 boss | `Setoid.ker f` → quotient → equivalence of quotient images | Setoid construction + quotient + sound/exact | W15–W16 |
| W17 boss | Lift + well-definedness + induction on quotient | `Quotient.lift`, well-def proof, `inductionOn` | W16–W17 |
| W18 boss | ℤ construction from ℕ × ℕ | Setoid, quotient, lift addition, well-definedness | W15–W17 all |
| W19 boss | Round-trip: equivalence classes partition + recover | Partition conditions + equivalence relation properties | W15–W19 |
| W20 boss | Choose correct notion of sameness per sub-goal | `=`, `≈`, `≃` discrimination | W15–W20 |
| W21 boss | Subtype construction + function application + ext | `⟨x, proof⟩`, coercion, `Subtype.ext` | W21 L01–L07 |
| W22 boss | Nontrivial Equiv construction + composition | 4-field construction + `Equiv.trans` | W22 L01–L06 |
| W23 boss | Build + verify PartialEquiv | Source/target + round-trip verification | W23 L01–L03 |
| W24 boss | `Equiv` between `↥s` and `↥t` via `BijOn` | Subtypes + equivs + on-set bijections | W21–W23 |
| W25 boss | Explicit injection + closure | Construction + image/subset closure chain | W25 L01–L08 |
| W26 boss | Diagonal argument on `ℕ → Bool` | Assume surjection, construct diagonal, contradict | W25–W26 |
| W27 boss | Concrete diagonal set construction | Build the missing set from a specific `f` | W25–W26 |
| W28 boss | Partition ↔ equivalence round-trip (full) | All major themes: sets, functions, quotients, equivs | All |

## 8. Transfer and Retrieval Plan

### High-value moves and their transfer chain

| Move | First appears | Supported practice | Reduced support | Fresh surface form | Plain-language transfer |
|------|--------------|-------------------|-----------------|--------------------|-----------------------|
| Unfold membership | W01 L02 | W01 L03–L06 | W03, W04 | W05 (ℤ, abstract sets) | "To check membership, evaluate the predicate" |
| Subset by `intro x hx` | W02 L01 | W02 L02–L04 | W03 L06–L07 | W05, W14 | "To show ⊆, take arbitrary element of LHS and show it's in RHS" |
| Set equality by `ext` | W02 L05 | W02 L06–L07 | W03 L08 | W05, W06, W08 | "Two sets are equal iff they have the same elements" |
| Image witness `⟨x, hx, rfl⟩` | W07 L01 | W07 L02–L04 | W08 | W28 | "To show something is in an image, find what maps to it" |
| Injectivity proof | W09 L01 | W09 L02–L03 | W12 | W13 (InjOn), W28 | "Assume equal outputs, derive equal inputs" |
| Surjectivity proof | W10 L01 | W10 L02–L03 | W12 | W13 (SurjOn), W28 | "Take arbitrary target, find its preimage" |
| Quotient lift | W17 L01 | W17 L02–L03 | W18 | W28 | "Well-definedness means the answer doesn't depend on the representative" |
| Diagonal argument | W26 L01–L03 | W26 L04–L05 | W27 | W27 (ℕ → ℕ), W28 | "Something always gets missed — construct the missing thing" |
| Partition ↔ equivalence | W19 L05–L06 | W19 L07 | W28 | W28 boss | "An equivalence relation chops a set into non-overlapping pieces" |

## 9. Misconception Plan

| Misconception | Where addressed | How |
|--------------|-----------------|-----|
| Sets are types | W01 introduction + W21 L06 | Explicit contrast: `{x \| p x}` vs `{x // p x}` |
| `↥s` changes type context silently | W21 L05 | Dedicated level exploring coercion |
| Image = preimage for inclusions | W07 L07–L08 | Prove both ⊆ directions; show equality requires inj/surj |
| `f '' (s ∩ t) = f '' s ∩ f '' t` | W07 L04 | Prove only ⊆; discuss failure of equality |
| `Equiv` = `Bijective` | W22 introduction + L05 | `Equiv` has data; `Bijective` is a proposition. `ofBijective` is noncomputable. |
| Quotient lift without well-definedness | W17 L03 | Explicit failure example: function that can't be lifted |
| `Countable` = `Encodable` | W25 L03–L04 | Side-by-side comparison |
| Cantor = uncountability of ℝ | W26 introduction | Explicit note: Cantor is about any `α → Set α`, not just ℝ |
| `≈` = `=` | W16, W20 | Dedicated world (W20) contrasting three notions |
| Partitions can have empty parts | W19 L04 | Counterexample: `∅` in a partition candidate |
| `InjOn f s` = `Injective f` | W13 L03 | Explicit counterexample |
| `BijOn` = `InjOn ∧ SurjOn` (missing MapsTo) | W13 L05 | Must prove all three components |
| `sᶜ` = `s \ t` for some `t` | W03 L03–L04 | Complement is `univ \ s`; difference is more general |

## 10. Major Risks

1. **Quotient section length**: Phase 5 has 6 worlds (W15–W20). This is the densest part of the course. Risk: learner fatigue. Mitigation: W20 (Three Sameness) is a short review/example world that breaks up the density. W18 (PsetRelations) provides retrieval practice before continuing to partitions.

2. **On-set function properties (W13–W14) may feel repetitive**: The proof shapes mirror global versions. Risk: boredom. Mitigation: focus on the *differences* (InjOn without Injective), keep the world tight, and use the pset for fresh problems rather than more of the same shape.

3. **Image/preimage asymmetry is subtle**: Learners will expect `f '' (s ∩ t) = f '' s ∩ f '' t`. Risk: confusion when only ⊆ holds. Mitigation: explicit worked example in W07 showing failure of equality, plus W08 retrieval, plus W28 showing how injectivity restores equality.

4. **Subtype/set notation confusion**: `{x | p x}` vs `{x // p x}` look similar. Risk: persistent confusion. Mitigation: explicit contrast level in W21, revisited in W24.

5. **Countability section may feel disconnected**: Phases 1–6 are about sets and functions; Phase 7 shifts to cardinality. Risk: the course feels like two courses stitched together. Mitigation: W25 and W26 heavily use injectivity/surjectivity (taught in Phase 3) and subtypes (Phase 6), making them genuine applications rather than standalone topics. W28 (Finale) ties everything back together.

6. **`Encodable`/`Denumerable` depth**: The coverage map marks these as core. Risk: too much time on constructive interfaces that the typical learner won't use. Mitigation: W25 introduces all three in sequence but keeps `Encodable`/`Denumerable` to 2 levels each. The boss focuses on `Countable` (the mathematical concept). If authoring reveals that `Encodable` internals don't provide good interactive levels, demote to supporting.

7. **Lattice alias exploit vector**: Set identities have lattice-level aliases that `exact` can find directly. Risk: learners bypass intended proofs. Mitigation: comprehensive `DisabledTheorem` list in the coverage map §6 must be applied at every relevant level. This is an operational burden on the world author.
