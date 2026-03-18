# PLAN: Functions & Relations

## 1. Course Promise

By the end of this course, the learner will be fluent in the foundational language of modern mathlib: sets as predicates, functions and their properties (injective, surjective, bijective), images and preimages, restriction to subsets, relations and equivalence relations, quotient constructions, bundled equivalences (`Equiv`), subtypes, and countability/encodability. The learner will understand the distinction between equality, equivalence, and isomorphism, and will be able to read and write proofs involving `Set`, `Function`, `Equiv`, `Quotient`, `Subtype`, and `Encodable` with confidence.

## 2. Learner Profile

- **Lean fluency**: NNG4-complete. Knows `intro`, `apply`, `exact`, `rfl`, `rw`, `cases`, `induction`, `constructor`, `left`, `right`, `exfalso`, `have`, `use`, `obtain`, `by_contra`.
- **Math background**: No serious prior mathematics required. Some informal intuitions about sets and functions from high school or early college are expected but not assumed.
- **Does NOT know**: `ext`, `push_neg`, `rintro`, `funext`, `calc`, `congr`, `specialize`, `change`, `show` (or may have seen these casually without practice).
- **Does NOT know**: The mathlib API for `Set`, `Function`, `Equiv`, `Quotient`, `Subtype`, `Encodable`.

## 3. Coverage Map (Summary)

Condensed from the full coverage map at `functions_relations/coverage-map.md`.

### Content Map

| Cluster | Core definitions | Core theorem families |
|---------|------------------|-----------------------|
| Sets | `Set α`, `∈`, `⊆`, `∅`, `Set.univ`, `{x \| P x}`, `∪`, `∩`, `\`, `ᶜ`, `⋃`, `⋂`, `Set.prod` | Set extensionality, de Morgan, distributive laws, indexed union/intersection distribution |
| Functions | `Injective`, `Surjective`, `Bijective`, `comp`, `id`, `LeftInverse`, `RightInverse`, `Involutive` | Composition preserves inj/surj/bij, left/right inverse characterizations |
| Image/Preimage | `Set.image`, `Set.preimage`, `Set.range` | Image/preimage interaction with set ops (preimage commutes with all; image does not commute with ∩ without injectivity) |
| Functions on Sets | `MapsTo`, `InjOn`, `SurjOn`, `BijOn`, `restrict`, `inclusion` | InjOn/SurjOn composition, BijOn characterization |
| Relations | Binary relation `α → α → Prop`, `Reflexive`, `Symmetric`, `Transitive`, `Antisymmetric` | Relation property independence, PER |
| Equivalence Relations | `Equivalence`, equivalence classes, partitions | Partition ↔ equivalence relation correspondence |
| Quotients | `Setoid`, `Quotient`, `Quotient.mk`, `Quotient.lift`, `Quotient.ind`, `Quotient.sound`, `Quotient.exact` | Well-definedness as the central difficulty |
| Equiv | `Equiv`, `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, `Equiv.ofBijective`, `Equiv.Perm` | Equiv construction, Equiv ≠ Bijective |
| Subtypes | `Subtype`, `Subtype.val`, `Subtype.property`, `↥s`, `Set.Elem` | Subtype coercion mechanics |
| Countability | `Set.Countable`, `Countable`, `Set.Finite`, Cantor's theorem | Diagonalization, countability of products/unions |
| Encodability | `Encodable`, `Denumerable`, Schröder-Bernstein | Concrete encoding constructions |

### Proof-Move Map

| Move | Where introduced | Where practiced | Where transferred |
|------|-----------------|-----------------|-------------------|
| Set extensionality (A = B via ∀ x, x ∈ A ↔ x ∈ B) | W1 | W2, W3, W5 | W8, boss levels |
| Double inclusion (A ⊆ B ∧ B ⊆ A → A = B) | W1 | W2, W5 | Boss levels |
| Membership chasing through set operations | W2 | W3, W5 | W8, W11 |
| Definition unfolding to expose quantifier structure | W1 | W6, W12 | Throughout |
| Witness exhibition for ∃ | W6 (surjectivity) | W7, W8, W13 | W16, boss levels |
| Preimage exhibition for image membership | W8 | W8, W9, W11 | Boss levels |
| Universal specialization | W1 (⊆ proofs) | W4, W6 | Throughout |
| Implication composition (chaining through two functions) | W6 | W8, W11 | Boss levels |
| Inverse construction | W6 | W7, W18 | Boss levels |
| Proof by contradiction | W6 (injectivity) | W12, W22 | Boss levels |
| Proof by contrapositive | W6 | W8 | — |
| Case splitting on ∨ / union membership | W2 | W3, W4, W5 | Boss levels |
| Working with ↔ (splitting, using each direction) | W1 | W2, W13 | Throughout |
| Well-definedness of quotient maps | W16 | W17 | W19 |
| Diagonalization | W22 | — | Boss (Cantor) |
| Function extensionality (funext) | W6 | W18 | — |
| Constructing an equivalence relation from scratch | W13 | W14 | W16 |
| Using antisymmetry (≤ both directions → =) | W12 | W14 | — |
| Building a function from cases | W6 | W10 | — |
| Induction on ℕ for countability | W22 | W23 | — |

### Lean Map

| Item | When introduced | Notes |
|------|----------------|-------|
| `ext` (set extensionality) | W1 | Dominant lesson of first real level |
| `push_neg` | W2 | For complement reasoning |
| `rintro ⟨⟩` | W2 | Pattern-matching intro |
| `specialize` | W1 | For ⊆ proofs |
| `change` / `show` | W1 | Rewriting goal to definitional equal |
| `simp` (with set lemmas) | W2 | Progressively enabled |
| `use` | W6 | Existential witness (may be known from NNG4) |
| `obtain ⟨a, ha, rfl⟩` | W8 | Destructuring image membership |
| `funext` | W6 | Function extensionality |
| `have` | W6 | Intermediate claims (may be known from NNG4) |
| `calc` | W12 | For transitivity chains |
| `congr` / `congr_arg` | W6 | — |
| `Quotient.lift` / `Quotient.mk` | W16 | Quotient API |
| `Equiv.mk` construction | W18 | Equiv API |
| `Subtype.mk` / `⟨val, property⟩` | W20 | Subtype API |
| `mem_image` / `mem_preimage` | W8 | Lemma family |

### Misconception Map

| Misconception | Where addressed | How |
|---------------|----------------|-----|
| "Sets are types" (no — `Set α` is `α → Prop`) | W1 (intro level) | Explicit docstring + level where this distinction matters |
| `f '' (A ∩ B) = f '' A ∩ f '' B` (false without injectivity) | W9 (counterexample level) + W8 (positive result) | Counterexample with specific f, A, B in W9 (ConcreteImages); positive result with injectivity is the W8 boss |
| "Symmetric + transitive → reflexive" (false — empty relation) | W14 (counterexample level) | Construct the empty relation on a nonempty type |
| "Bijective = Equiv" (no — Bijective is Prop, Equiv carries data) | W18 (explicit comparison level) | Level contrasting the two; then Equiv.ofBijective |
| "Quotient.lift just works" (no — needs well-definedness) | W16 (level where well-def fails) | Level where the learner must prove the well-def condition |
| "⊆ and ⊂ confusion" | W1 (docstring warning) | Warning + note in intro |
| "Equivalence relation ≠ Equiv" (completely different) | W19 (explicit naming level) | Dedicated comparison in the consolidation world |
| "Complement is ᶜ not - or ~" | W2 (notation doc) | Notation teaching level |
| "Image notation '' ≠ string quotes" | W8 (doc warning) | Docstring warning |
| "Countable includes finite" | W22 (explicit level) | Level proving a finite set is countable |
| "Antisymmetric ≠ not-symmetric" | W12 (docstring) + W14 (counterexample) | ≤ on ℕ: both antisymmetric AND symmetric on singletons |
| "Set.restrict changes the codomain" (it doesn't) | W10 (docstring warning) | Warning + level demonstrating restrict |

## 4. Granularity Plan

### World scale

Each world has **one center of gravity**: a single theorem family, a single proof-shape cluster, a single mathematical object (for example worlds), or a bounded integration task (for pset/review worlds).

**Split triggers** (any of these means the world should be split):
- Two unrelated theorem families forced into one world intro
- A level that requires a move not introduced by any earlier level in the same world
- Cognitive overload: more than 3 new notation symbols introduced in a single world

**Merge triggers** (any of these means the material should be absorbed):
- Fewer than 4 levels of material
- The material is a single definition with no interesting proof structure

### Level scale

Each level has **one dominant lesson**. The dominant lesson is the answer to: "What move is this level really about?" Every other element of the level (notation, definitions, tactics) should be held constant or already learned.

**One new thing per level**: either a new proof move, a new tactic, a new definition, or a new notation — never more than one.

### No level count targets

Worlds contain as many levels as the learner needs. No minimum or maximum. The only question is: does each level teach something new or provide necessary practice?

## 5. World Graph

### Cluster 1: Sets

---

#### W1: SetsAndMembership
**Type**: Lecture
**Promise**: By the end of this world, the learner can define sets as predicates, prove membership, prove subset relationships, and prove two sets are equal using extensionality.
**Center of gravity**: `Set α` as `α → Prop`, `∈`, `⊆`, `∅`, `Set.univ`, set-builder notation, set extensionality, double inclusion.
**Proof-move goals**:
- Set extensionality: prove A = B by `∀ x, x ∈ A ↔ x ∈ B`
- Double inclusion: prove A = B by `A ⊆ B ∧ B ⊆ A`
- Unfolding a definition to see its logical structure
- Specializing a ∀ hypothesis
- Working with ↔
**Inventory changes**:
- NEW tactics: `ext`, `specialize`, `change`, `show`, `unfold`
- NEW definitions: `Set`, `Set.mem`, `HasSubset.Subset` (for sets), `Set.empty`, `Set.univ`, set-builder
- NEW theorems: `Set.ext_iff`, `Set.Subset.antisymm`
- DISABLED: `trivial`, `decide`, `simp`, `aesop`, `simp_all`, `tauto`, `norm_num`
**Boss**: Prove `Set.Subset.antisymm` — if `A ⊆ B` and `B ⊆ A` then `A = B`. Requires `ext`, ↔ splitting, and using both subset hypotheses. This integrates the world's three main moves (extensionality, ↔, specialization).
**Dependencies**: None (first world).
**Levels (estimated)**: 8–10

---

#### W2: SetOperations
**Type**: Lecture
**Promise**: By the end of this world, the learner can prove identities involving union, intersection, difference, and complement, including de Morgan laws and distributive laws.
**Center of gravity**: `∪`, `∩`, `\`, `ᶜ`, de Morgan laws, distributive laws.
**Proof-move goals**:
- Membership chasing through set operations
- Case splitting on ∨ / union membership
- Push negation for complement reasoning
**Inventory changes**:
- NEW tactics: `push_neg`, `rintro ⟨⟩`, `left`, `right`, `rcases`
- NEW definitions: `Set.union`, `Set.inter`, `Set.diff`, `Set.compl`
- NEW notation: `∪`, `∩`, `\`, `ᶜ`
- ENABLE: `simp` with set simp lemmas (after learner has done at least 3 levels by hand)
- DISABLED: `tauto` (closes too many propositional goals), lattice lemmas (`sup_comm`, `inf_comm`, etc.)
**Boss**: Prove de Morgan: `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`. Requires `ext`, complement unfolding, `push_neg`, and case analysis on membership. Integrates all main moves.
**Dependencies**: W1.
**Levels (estimated)**: 8–10

---

#### W3: ConcreteSets
**Type**: Example
**Promise**: By the end of this world, the learner has worked with specific named sets of natural numbers, computed concrete set operations, and seen that set algebra identities are not just formal exercises but describe real mathematical objects.
**Center of gravity**: Specific sets — evens, odds, primes, finite set literals `{1, 2, 3}`. Concrete membership, subset, intersection, union, complement computations.
**Example/counterexample roster**:
- Verify `3 ∈ {n : ℕ | n > 2}`
- Verify `{1, 2} ⊆ {1, 2, 3}`
- Compute `{1,2,3} ∩ {2,3,4}` on a suitable type
- Compute a union of specific sets
- Complement of evens = odds (on ℕ or a finite type)
- De Morgan on specific finite sets
- Counterexample: `A ⊂ B` does not mean `A = B`
**Inventory changes**: No new tactics. May introduce `norm_num` or `decide` in a controlled way for specific computations on finite types, then re-disable.
**Boss**: Multi-step computation: prove a chain of set equalities involving concrete sets, combining intersection, union, and complement.
**Dependencies**: W1, W2.
**Levels (estimated)**: 7–9

---

#### W4: IndexedFamilies
**Type**: Lecture
**Promise**: By the end of this world, the learner can work with indexed unions and intersections, prove distribution identities, and handle set-of-sets variants.
**Center of gravity**: `⋃ i, f i`, `⋂ i, f i`, `Set.sUnion`, `Set.sInter`, `Set.prod`, `Set.powerset`.
**Proof-move goals**:
- Membership chasing through indexed unions/intersections (∃ i, x ∈ f i for union; ∀ i, x ∈ f i for intersection)
- Specializing the index variable
- Combining indexed operations with binary operations
- Working with set-of-sets: powerset membership (s ∈ 𝒫 A ↔ s ⊆ A)
**Inventory changes**:
- NEW definitions: `Set.iUnion`, `Set.iInter`, `Set.sUnion`, `Set.sInter`, `Set.prod`, `Set.powerset`
- NEW notation: `⋃ i, f i`, `⋂ i, f i`, `𝒫` (Set.powerset)
- NEW lemmas: `Set.mem_iUnion`, `Set.mem_iInter`, `Set.mem_sUnion`, `Set.mem_sInter`, `Set.mem_powerset_iff`
**Powerset coverage**: 1–2 levels on `Set.powerset`. The powerset is the prototypical "set of sets" — membership in `𝒫 A` is equivalent to `⊆ A`. This connects naturally to the indexed families theme and provides important foreshadowing for Cantor's theorem (W22), where the key insight is that no function from a set to its power set can be surjective.
**Boss**: Prove `A ∩ (⋃ i, f i) = ⋃ i, (A ∩ f i)` — intersection distributes over indexed union. Requires `ext`, membership chasing through both ∩ and ⋃, and existential management. Seeded by: W1 (ext), W2 (intersection membership), W4 earlier levels (indexed union membership).
**Dependencies**: W1, W2.
**Levels (estimated)**: 8–11

---

#### W5: SetsPset
**Type**: Pset
**Promise**: By the end of this world, the learner can solve mixed set problems with reduced scaffolding, retrieving techniques from W1–W4 without explicit prompting.
**Center of gravity**: Retrieval and transfer. Problems that combine set extensionality, membership chasing, set operations, indexed families, and double inclusion — without telling the learner which technique to use.
**Proof-move goals**: All moves from W1–W4, with less scaffolding. Learner must choose the right approach.
**Inventory changes**: All W1–W4 inventory available. No new items.
**Boss**: A problem requiring indexed union/intersection + set algebra + extensionality in a single proof. Something like: prove `(⋃ i, f i) \ A = ⋃ i, (f i \ A)`, or a multi-step argument that requires choosing between ext and double inclusion.
**Dependencies**: W1–W4.
**Levels (estimated)**: 6–8

---

### Cluster 2: Functions

---

#### W6: FunctionProperties
**Type**: Lecture
**Promise**: By the end of this world, the learner can prove that specific functions are injective, surjective, or bijective, prove that compositions preserve these properties, and work with left/right inverses.
**Center of gravity**: `Function.Injective`, `Function.Surjective`, `Function.Bijective`, `Function.comp`, `id`, `Function.LeftInverse`, `Function.RightInverse`, `Function.Involutive`.
**Proof-move goals**:
- Injectivity: assume f(a) = f(b), show a = b
- Surjectivity: given y, construct x with f(x) = y
- Proof by contradiction (for injectivity of specific functions)
- Proof by contrapositive
- Implication composition (inj ∘ inj, surj ∘ surj)
- Inverse construction
- Function extensionality (funext)
**Inventory changes**:
- NEW tactics: `funext`, `congr`
- NEW definitions: `Function.Injective`, `Function.Surjective`, `Function.Bijective`, `Function.LeftInverse`, `Function.RightInverse`, `Function.Involutive`
- NEW theorems: `Function.Injective.comp`, `Function.Surjective.comp`, left/right inverse characterizations
**Left inverse constructivity**: Include a **dedicated level** (not just a docstring) addressing the constructivity edge case for left inverses. In classical mathematics, every injective function has a left inverse — but constructing one requires choosing a default value for the complement of the range, which is non-constructive (requires `Classical.choice` or equivalent). On the empty domain, the statement is vacuously true but the construction is degenerate. The level should have the learner attempt to construct a left inverse for a specific injective function and encounter the need for `Classical.choice` (via `Function.invFun` or `Classical.arbitrary`). The docstring should explain why classical reasoning is needed and what it means for constructivity. This makes the edge case concrete rather than expository.
**Boss**: Prove that the composition of two bijections is bijective. Requires: unfold `Bijective` into `Injective ∧ Surjective`, prove each half using composition lemmas from earlier levels. Seeded by: separate levels on inj∘inj and surj∘surj earlier in the world.
**Dependencies**: W1 (∀ and ∃ reasoning from ⊆ proofs).
**Levels (estimated)**: 9–11

---

#### W7: ConcreteFunctions
**Type**: Example
**Promise**: By the end of this world, the learner has verified injectivity/surjectivity for specific named functions, seen concrete counterexamples, and understands how function properties manifest on real mathematical objects.
**Center of gravity**: Specific functions on ℕ, ℤ, and small types.
**Example/counterexample roster**:
- `(· + 1)` on ℕ: injective (prove it)
- `(· + 1)` on ℕ: NOT surjective (0 has no preimage — prove it)
- `(· * 2)` on ℕ: injective (prove it)
- A concrete non-injective function with specific counterexample witnesses
- Negation on ℤ: bijective, involutive
- A concrete composition: verify inj ∘ inj on specific functions
- Counterexample: a surjection composed with an injection that is NOT bijective (order matters for composition)
- Construct a concrete left inverse for a specific injective function
**Inventory changes**: No new tactics or definitions. Concrete lemmas about ℕ/ℤ arithmetic may be enabled as needed.
**Boss**: Verify a specific function (e.g., negation on ℤ, or a carefully chosen function between Fin types) is bijective and construct its inverse function explicitly.
**Dependencies**: W6.
**Levels (estimated)**: 8–10

---

#### W8: ImageAndPreimage
**Type**: Lecture
**Promise**: By the end of this world, the learner can prove membership in images and preimages, prove set equalities involving images and preimages, and understands the asymmetry between image and preimage with respect to set operations.
**Center of gravity**: `Set.image` (`f '' S`), `Set.preimage` (`f ⁻¹' S`), `Set.range`, interaction with ∪, ∩, ᶜ.
**Proof-move goals**:
- Exhibiting a preimage for image membership: given `x ∈ f '' S`, extract `a ∈ S` with `f a = x`
- Constructing image membership: given `a ∈ S`, show `f a ∈ f '' S`
- Destructuring: `obtain ⟨a, ha, rfl⟩`
- Image commutes with union: `f '' (A ∪ B) = f '' A ∪ f '' B`
- Preimage commutes with all set operations
- Image does NOT commute with intersection (without injectivity)
- Under injectivity: `f '' (A ∩ B) = f '' A ∩ f '' B`
**Inventory changes**:
- NEW notation: `''` (Set.image), `⁻¹'` (Set.preimage)
- NEW definitions: `Set.image`, `Set.preimage`, `Set.range`
- NEW lemmas: `Set.mem_image`, `Set.mem_preimage`, `Set.image_union`, `Set.preimage_inter`, etc.
- TEACH: `obtain ⟨a, ha, rfl⟩` pattern (critical for this world)
**Novelty management**: First level introduces `''` and `⁻¹'` notation with trivial proofs (unfolding only). Second level introduces image membership proof shape. Third level practices. Notation and proof move are NOT introduced in the same level.
**Boss**: Prove the injective-image-intersection theorem: if `f` is injective, then `f '' (A ∩ B) = f '' A ∩ f '' B`. Requires: ext, image membership reasoning in both directions, and using the injectivity hypothesis in the hard direction (⊇). Seeded by: earlier levels on `f '' (A ∪ B)` (easy direction) and `f '' A ∩ f '' B ⊆ f '' (A ∩ B)` (the hard step, practiced with support).
**Dependencies**: W2 (set operations), W6 (injectivity).
**Levels (estimated)**: 9–11

---

#### W9: ConcreteImages
**Type**: Example
**Promise**: By the end of this world, the learner has computed specific images and preimages, seen the image/intersection asymmetry on concrete examples, and understands how image/preimage notation maps onto real mathematical objects.
**Center of gravity**: Concrete image and preimage computations on specific functions and sets of ℕ/ℤ. Counterexample for the image/intersection misconception.
**Example/counterexample roster**:
- Compute `f '' {1, 2, 3}` for a specific function (e.g., `(· * 2)` on ℕ) — direct image computation
- Compute `f ⁻¹' {2, 4, 6}` for a specific function — direct preimage computation
- Verify `f '' (A ∪ B) = f '' A ∪ f '' B` on specific sets (positive result, concrete)
- **Counterexample**: Specific `f`, `A`, `B` where `f '' (A ∩ B) ≠ f '' A ∩ f '' B` — the most important counterexample in the course. Use a non-injective function (e.g., a constant or collapsing function) with carefully chosen disjoint or overlapping sets.
- Compute `Set.range` for a specific function
- Verify a preimage identity (e.g., `f ⁻¹' (S ∩ T) = f ⁻¹' S ∩ f ⁻¹' T`) on concrete sets
**Inventory changes**: No new tactics or definitions. All W8 inventory available. May need `norm_num` or `decide` enabled per-level for arithmetic.
**Boss**: Construct a concrete counterexample to `f '' (A ∩ B) = f '' A ∩ f '' B`: define a specific function and two specific sets, show the left side is strictly contained in the right side (or that a specific element is in one but not the other). This makes the image/intersection asymmetry visceral, not abstract.
**Dependencies**: W8.
**Levels (estimated)**: 5–7

---

#### W10: FunctionsOnSets
**Type**: Lecture
**Promise**: By the end of this world, the learner can work with `MapsTo`, `InjOn`, `SurjOn`, `BijOn`, and `restrict`, and understands how these "on a set" variants relate to their global counterparts.
**Center of gravity**: `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`, `Set.restrict`, `Set.inclusion`.
**Proof-move goals**:
- Restricting a global property to a set (Injective → InjOn)
- Proving MapsTo for a specific function and set
- Proving InjOn directly (the key concept — different from Injective)
- SurjOn and BijOn following the InjOn pattern
- Using restrict to create a function with a subtype domain
**Inventory changes**:
- NEW definitions: `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`, `Set.restrict`, `Set.inclusion`
- NEW theorems: `Set.InjOn.comp`, `Set.MapsTo.restrict`, `Injective → InjOn` (global to local), `InjOn + SurjOn → BijOn`
**Boss**: Prove that if `f.InjOn s` and `f.SurjOn s t`, then `f.BijOn s t`. This integrates InjOn and SurjOn from earlier levels and requires understanding of BijOn as the conjunction.
**Dependencies**: W6, W8.
**Levels (estimated)**: 8–10

---

#### W11: FunctionsPset
**Type**: Pset
**Promise**: By the end of this world, the learner can solve mixed problems about functions, images, preimages, and functions-on-sets with reduced scaffolding.
**Center of gravity**: Retrieval and transfer across W6–W10. Problems that require choosing between injectivity/surjectivity proof shapes, image/preimage reasoning, and on-a-set variants.
**Proof-move goals**: All moves from W6–W10. Learner must choose the right technique.
**Inventory changes**: All W6–W10 inventory. No new items.
**Boss**: A problem integrating multiple function concepts: e.g., prove that if `f` is bijective and maps `s` onto `t`, then `f⁻¹` maps `t` onto `s` — or a multi-step argument combining image, preimage, and injectivity.
**Dependencies**: W6–W10.
**Levels (estimated)**: 6–8

---

### Cluster 3: Relations

---

#### W12: BinaryRelations
**Type**: Lecture
**Promise**: By the end of this world, the learner can define binary relations, verify reflexivity/symmetry/transitivity/antisymmetry, and understands that these properties are independent.
**Center of gravity**: Binary relation `α → α → Prop`, `Reflexive`, `Symmetric`, `Transitive`, `Antisymmetric`. Partial equivalence relations (PER: symmetric + transitive).
**Proof-move goals**:
- Unfolding a relation definition to see its logical structure
- Verifying each property independently
- Using transitivity in chain arguments
- Using antisymmetry (≤ in both directions → =)
- `calc` blocks for transitivity chains
**Inventory changes**:
- NEW tactics: `calc`
- NEW definitions: `Reflexive`, `Symmetric`, `Transitive`, `Antisymmetric`, `IsTrans`, PER
- NEW theorems: basic relation property lemmas
- DISABLED: `tauto` (closes many propositional relation goals)
**PER coverage**: 1–2 levels on partial equivalence relations (symmetric + transitive but not necessarily reflexive). This is explicitly in scope. Introduce after the four main properties.
**Boss**: Prove that a PER (symmetric + transitive relation) is reflexive on its domain: `∀ x y, R x y → R x x`. Proof sketch: from `R x y`, derive `R y x` by symmetry, then `R x x` by transitivity (applied to `R x y` and `R y x`). This integrates PER (the world's culminating concept), symmetry, transitivity, and definition-unfolding — the world's four main moves. Seeded by: symmetry levels, transitivity levels, and PER introduction levels.
**Dependencies**: W1 (∀ reasoning).
**Levels (estimated)**: 8–10

---

#### W13: EquivalenceRelations
**Type**: Lecture
**Promise**: By the end of this world, the learner can verify that a relation is an equivalence relation, compute equivalence classes, and understands the partition ↔ equivalence relation correspondence.
**Center of gravity**: `Equivalence`, equivalence classes, partitions, partition ↔ equivalence relation correspondence.
**Proof-move goals**:
- Constructing an equivalence relation from scratch (verify refl, symm, trans)
- Computing equivalence classes (the class of x is {y | x ~ y})
- Proving two elements are in the same class iff they are related
- Partition → equivalence relation direction
- Equivalence relation → partition direction (classes are nonempty, disjoint, cover the type)
**Inventory changes**:
- NEW definitions: `Equivalence`, `Setoid.classes`, equivalence class
- NEW theorems: class membership lemmas, partition characterization
**Boss**: One direction of the partition ↔ equivalence relation correspondence: given an equivalence relation, prove that its classes form a partition (nonempty, pairwise disjoint, covering). This is multi-step but all sub-steps have been seeded in earlier levels. Seeded by: class nonemptiness (from reflexivity level), class disjointness (from transitivity + symmetry level), coverage (from class membership level).
**Dependencies**: W12.
**Levels (estimated)**: 8–10

---

#### W14: ConcreteRelations
**Type**: Example
**Promise**: By the end of this world, the learner has verified relation properties for specific named relations, seen critical counterexamples that separate the properties, and computed specific equivalence classes.
**Center of gravity**: Specific relations on ℕ, ℤ, and small finite types.
**Example/counterexample roster**:
- Congruence mod 2 on ℤ: verify reflexive, symmetric, transitive → equivalence relation
- "Same parity" on ℕ: verify as equivalence relation
- **Counterexample**: the empty relation `fun (_ _ : ℕ) ↦ False` — symmetric and transitive but NOT reflexive
- **Counterexample**: a reflexive+symmetric relation that is NOT transitive (on a small finite type)
- ≤ on ℕ: reflexive, transitive, antisymmetric but NOT symmetric
- **Counterexample**: antisymmetric does NOT mean not-symmetric (the identity relation is both)
- Compute equivalence classes of mod 2 on ℤ (the two classes: evens and odds)
**Inventory changes**: May need `omega`, `norm_num`, or `decide` enabled for specific arithmetic computations on ℤ/ℕ, then re-disabled.
**Boss**: Verify that a moderately complex relation (e.g., congruence mod 3, or a custom relation on a small type) is an equivalence relation, then identify one of its equivalence classes.
**Dependencies**: W12, W13.
**Levels (estimated)**: 8–10

---

#### W15: RelationsPset
**Type**: Pset
**Promise**: By the end of this world, the learner can solve mixed problems about relations, equivalence relations, and partitions with reduced scaffolding.
**Center of gravity**: Retrieval and transfer across W12–W14. Problems require identifying which relation properties apply, constructing equivalence relations, and connecting to partition structure.
**Inventory changes**: All W12–W14 inventory. No new items.
**Boss**: A multi-step problem: given a relation, determine whether it is an equivalence relation, and if so, describe the partition it induces. Or: given a partition, construct the corresponding equivalence relation and verify it.
**Dependencies**: W12–W14.
**Levels (estimated)**: 6–8

---

### Cluster 4: Quotients and Bundled Equivalences

---

#### W16: Quotients
**Type**: Lecture
**Promise**: By the end of this world, the learner can construct setoids, form quotient types, lift functions through quotients (with well-definedness proofs), and use quotient induction.
**Center of gravity**: `Setoid`, `Quotient`, `Quotient.mk` / `⟦·⟧`, `Quotient.lift`, `Quotient.ind`, `Quotient.sound`, `Quotient.exact`.
**Proof-move goals**:
- Constructing a Setoid from an Equivalence (familiar from W13)
- Using `⟦x⟧` notation for Quotient.mk
- Proving well-definedness: the central move. "If a ~ b then f(a) = f(b)"
- Lifting a function through a quotient using Quotient.lift
- Using Quotient.ind to prove ∀ statements about quotient elements
- Using Quotient.sound to show `⟦a⟧ = ⟦b⟧` from `a ~ b`
**Novelty management**: This is a novelty hotspot. Level sequence:
1. Construct a Setoid (familiar move from W13, new bundling)
2. Introduce `⟦x⟧` notation (trivial proof, notation focus only)
3. Introduce well-definedness as a concept (docstring + first attempt)
4. Prove well-definedness for a simple function
5. Use `Quotient.lift` with the well-def proof from the previous level
6. Practice lift on a different function
7. Introduce `Quotient.ind` for ∀ on quotients
8. Introduce `Quotient.sound` and `Quotient.exact`
9. Integration: lift + property proof
10. Boss
**Inventory changes**:
- NEW notation: `⟦·⟧` (`\[[` and `\]]`)
- NEW definitions: `Setoid`, `Quotient`, `Quotient.mk`, `Quotient.lift`, `Quotient.ind`, `Quotient.sound`, `Quotient.exact`
**Boss**: Lift a nontrivial function through a quotient, prove well-definedness, and then prove a property of the lifted function using Quotient.ind. This integrates all main moves. Seeded by: well-def levels (step 4–6), lift levels (5–6), ind level (7).
**Dependencies**: W13 (equivalence relations).
**Levels (estimated)**: 9–11

---

#### W17: ConcreteQuotients
**Type**: Example
**Promise**: By the end of this world, the learner has constructed specific quotients (ℤ mod n), lifted specific functions through them, and seen how abstract quotient machinery operates on real mathematical objects.
**Center of gravity**: ℤ mod 2, ℤ mod 3, or ℤ mod n as concrete quotients.
**Example roster**:
- Construct the Setoid for congruence mod 2 on ℤ
- Show that specific elements are equivalent: `⟦0⟧ = ⟦2⟧` in ℤ mod 2
- Lift the absolute-value function (or another suitable function) through the quotient, proving well-definedness
- Show that a function that does NOT respect the equivalence CANNOT be lifted (well-def fails)
- Work with ℤ mod 3: a second quotient to practice the same moves on a different object
- Use Quotient.ind on a concrete quotient
**Inventory changes**: Arithmetic lemmas for ℤ as needed.
**Boss**: Lift addition (or a simpler operation) through ℤ mod n and prove a property of the result.
**Dependencies**: W16, W14 (concrete mod n relations).
**Levels (estimated)**: 7–9

---

#### W18: BundledEquiv
**Type**: Lecture
**Promise**: By the end of this world, the learner can construct `Equiv` values, use `Equiv.refl`/`symm`/`trans`, and understands the crucial distinction between `Bijective` (a Prop) and `Equiv` (data carrying the inverse).
**Center of gravity**: `Equiv α β`, `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, `Equiv.toFun`, `Equiv.invFun`, `Equiv.ofBijective`, `Equiv.Perm`.
**Proof-move goals**:
- Constructing an Equiv by providing both functions and both proofs (left_inv, right_inv)
- Using Equiv.refl/symm/trans
- Using Equiv.ofBijective to convert a bijection proof to data
- Understanding that Equiv carries data (the inverse function) while Bijective is purely propositional
**Inventory changes**:
- NEW notation: `≃` (`\simeq`)
- NEW definitions: `Equiv`, `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, `Equiv.toFun`, `Equiv.invFun`, `Equiv.ofBijective`, `Equiv.Perm`
- NEW theorems: `Equiv.left_inv`, `Equiv.right_inv`
**Boss**: Construct an `Equiv` from scratch: provide both functions and prove both inverse conditions. Then show that `Equiv.toFun` is bijective. This is the full round-trip from data to Prop and back. Seeded by: Equiv.mk levels (steps 2–4), bijective proof levels (W6).
**Dependencies**: W6 (bijections, inverses).
**Levels (estimated)**: 8–10

---

#### W19: EqualityEquivalenceIsomorphism
**Type**: Review / Consolidation
**Promise**: By the end of this world, the learner understands the three levels of "sameness" in mathematics and in Lean: propositional equality (`=`), equivalence relations (Setoid/Quotient), and type isomorphisms (Equiv). The learner can articulate when to use each and navigate between them.
**Center of gravity**: Comparing equality, equivalence relations, and Equiv. This is explicitly required by the course description: "the difference between equality, equivalence, and isomorphism."
**Key levels**:
- Level contrasting `=` (definitional/propositional) with `Setoid.r` (user-defined)
- Level contrasting `Equivalence` (a property of a relation) with `Equiv` (a data type)
- Level where using the wrong notion leads to a stuck proof
- Level where the learner converts between the notions (e.g., `Equiv.ofBijective`, `Quotient.sound`)
- Transfer level: "In ordinary mathematics, when do we use '=', '≡', and '≅'?"
**Inventory changes**: All earlier inventory. No new items. This world is about integration, not new material.
**Boss**: A multi-step problem that requires navigating between at least two of the three notions. E.g., given an equivalence relation on a type, form the quotient, construct an Equiv between the quotient and another type, and use it to transfer a property.
**Dependencies**: W13 (equivalence relations), W16 (quotients), W18 (Equiv).
**Levels (estimated)**: 6–8

---

### Cluster 5: Subtypes and Countability

---

#### W20: Subtypes
**Type**: Lecture
**Promise**: By the end of this world, the learner can construct subtype values, extract data and proofs from subtypes, work with the `↥s` coercion, and move between `Set α` and `Subtype` viewpoints.
**Center of gravity**: `Subtype` (`{x : α // P x}`), `Subtype.val`, `Subtype.property`, `Subtype.mk`, `↥s` (Set-to-Subtype coercion), `Set.Elem`.
**Proof-move goals**:
- Constructing a subtype element: `⟨val, proof⟩`
- Extracting the value: `Subtype.val` or `↑`
- Extracting the proof: `Subtype.property`
- Working with invisible coercions (`↥s` often appears implicitly in goals)
- Converting between set membership and subtype membership
**Novelty management**: This is a novelty hotspot (new notation: `{x // P x}`, `↥s`, `↑`, `Set.Elem`). Level sequence:
1. Introduce `{x : α // P x}` syntax with a trivial construction
2. Extract value and proof from a subtype element
3. Introduce `↑` as coercion notation
4. Introduce `↥s` — set-as-subtype coercion
5. A level where coercion is invisible in the goal (teaching the learner to recognize it)
6. Convert between set membership and subtype viewpoint
7. Construct a function on a subtype
8. Boss
**Inventory changes**:
- NEW notation: `{x // P x}`, `↑`, `↥`
- NEW definitions: `Subtype`, `Subtype.val`, `Subtype.property`, `Subtype.mk`, `Set.Elem`
**Boss**: Given a set `s : Set α` and a function `f : α → β`, construct the restricted function `↥s → β` and prove a property (e.g., if `f` is injective then the restriction is injective). Integrates subtype construction, coercion, and function properties.
**Dependencies**: W1 (sets), W6 (function properties).
**Levels (estimated)**: 8–10

---

#### W21: ConcreteSubtypes
**Type**: Example
**Promise**: By the end of this world, the learner has worked with specific subtypes of ℕ (even numbers, bounded numbers), constructed Equivs involving subtypes, and seen how subtypes concretize the abstract set/function machinery.
**Center of gravity**: Specific subtypes and Equivs.
**Example roster**:
- Construct a specific element of `{n : ℕ // Even n}` (e.g., `⟨4, by omega⟩`)
- Work with `{n : ℕ // n < 5}` and its inhabitants
- Prove `Bool ≃ Fin 2` or `Fin n ≃ {i : ℕ // i < n}` (or use a simpler concrete Equiv)
- A function between two concrete subtypes
- Subtype.val on a specific subtype
- Connection: if `x : {n : ℕ // Even n}`, then `x.val` is even — use `x.property`
**Inventory changes**: `Fin` API as needed. May need `omega` or `norm_num` for arithmetic.
**Boss**: Construct an `Equiv` between two concrete subtypes (or between a subtype and `Fin n`), providing both directions and both proofs.
**Dependencies**: W20, W18 (Equiv).
**Levels (estimated)**: 6–8

---

#### W22: Countability
**Type**: Lecture
**Promise**: By the end of this world, the learner understands countability, can prove specific sets are countable, understands that finite implies countable, and has seen Cantor's theorem (no surjection from a set to its power set) via diagonalization.
**Center of gravity**: `Set.Countable`, `Countable` (typeclass), `Set.Finite`, Cantor's theorem.
**Proof-move goals**:
- Proving countability via injection into ℕ or surjection from ℕ
- Finite → countable
- Countable unions of countable sets are countable
- Diagonalization argument (Cantor): define the diagonal set, assume surjectivity, derive contradiction
- Induction on ℕ for countability constructions
**Inventory changes**:
- NEW definitions: `Set.Countable`, `Countable`, `Set.Finite`
- NEW theorems: `Set.Countable.union`, `Set.Finite.countable`, Cantor's theorem
- ENABLE: `by_contra` should be emphasized here (may already be known from NNG4)
**Cantor/powerset connection**: Include a docstring in the Cantor's theorem level (or a preceding level) connecting the diagonal argument to the power set concept from W4. Cantor's theorem says no surjection `α → Set α` exists — and `Set α` is morally the power set of `α`. The docstring should note: "The set `Set α` of all subsets of `α` is the power set 𝒫(α) that you saw in W4. Cantor's theorem says this power set is always strictly larger than `α` itself — there is no way to enumerate all subsets." This connects the abstract diagonal argument back to the concrete set-of-sets intuition the learner built earlier.
**Boss**: Cantor's theorem: prove that there is no surjection `α → Set α`. The diagonalization argument constructs `s = {x | x ∉ f x}` and derives a contradiction. This is the most famous argument in the course. Seeded by: earlier levels that practice contradiction, set membership, and the diagonal construction step-by-step. The boss should NOT introduce the diagonal construction for the first time — earlier levels must seed it.
**Dependencies**: W1 (sets), W4 (indexed families), W6 (injective/surjective).
**Levels (estimated)**: 9–11

---

#### W23: Encodability
**Type**: Lecture
**Promise**: By the end of this world, the learner can work with `Encodable` and `Denumerable`, construct concrete encodings, and understands Schröder-Bernstein as a tool for proving countability.
**Center of gravity**: `Encodable`, `Denumerable`, concrete encoding constructions, Schröder-Bernstein theorem.
**Proof-move goals**:
- Constructing an `Encodable` instance by providing `encode` and `decode` with a round-trip proof
- Using `Encodable` instances for products, sums, etc.
- Understanding `Denumerable` as the countably-infinite variant
- Schröder-Bernstein: if there exist injections `α → β` and `β → α`, then `α ≃ β` (used as a tool, not proved from scratch — the proof is too complex for a basic course)
- **ℕ-induction for encoding constructions**: At least one level must use induction on ℕ to build or verify an encoding — e.g., proving that an encoding function is surjective onto ℕ, or constructing a decode function by induction. This backs up the Section 3 proof-move map claim that ℕ-induction is practiced in W23.
**Inventory changes**:
- NEW definitions: `Encodable`, `Encodable.encode`, `Encodable.decode`, `Denumerable`
- NEW theorems: `Encodable.prod`, `Encodable.sum`, Schröder-Bernstein
**Boss**: Prove that `ℕ × ℕ` is `Encodable` (or `Countable`) by constructing the encoding explicitly or by using the product instance + Schröder-Bernstein. This integrates encoding construction, product structure, and the Equiv/injection machinery.
**Dependencies**: W18 (Equiv), W22 (countability).
**Levels (estimated)**: 8–10

---

#### W24: SubtypesCountabilityPset
**Type**: Pset / Consolidation
**Promise**: By the end of this world, the learner can solve mixed problems integrating subtypes, countability, and encodability with reduced scaffolding, choosing the right technique without prompting. This world also provides concrete countability and encodability examples that W22 and W23 (both lecture worlds) did not dedicate levels to.
**Center of gravity**: Retrieval and transfer across W20–W23. Problems require choosing between subtype construction, countability arguments, encoding constructions, and Equiv without being told which to use.
**Proof-move goals**: All moves from W20–W23 in mixed contexts. The learner must:
- Decide when to construct a subtype vs. use set membership
- Choose between proving countability via injection, surjection, or Encodable instance
- Construct concrete encodings without templates
- Combine subtype and Equiv machinery in a single proof
**Exercise roster**:
- Prove a specific subtype is countable (e.g., `{n : ℕ // Even n}` is countable) — requires combining subtype machinery with countability
- Prove ℤ is countable — concrete countability exercise
- Encode a specific pair (e.g., construct the encoding of `(3, 7) : ℕ × ℕ`) — concrete encoding exercise
- Is a finite set countable? Prove it concretely on a specific finite type
- Construct an Equiv involving a subtype and `Fin`
- A problem combining subtype restriction with image/preimage and countability
- A problem requiring the learner to choose between Encodable and Set.Countable approaches
**Inventory changes**: All W20–W23 inventory available. No new items.
**Boss**: Prove that a subtype `{x : α // P x}` is countable when `α` is countable and `P` is decidable, or construct an Equiv between two encodable types using Schröder-Bernstein and subtype machinery. The boss should integrate subtypes, countability, and encoding in a single multi-step proof — bringing together the course's final cluster.
**Dependencies**: W20–W23.
**Levels (estimated)**: 7–9

---

## 6. Inventory Release Plan

### Global disables (all worlds)

| Item | Reason |
|------|--------|
| `trivial` | Closes trivially true goals without learning |
| `decide` | Closes decidable goals without learning |
| `native_decide` | Same |
| `simp_all` | Too powerful for a teaching context |
| `aesop` | Solves many membership/extensionality goals |
| `tauto` | Closes propositional goals (set theory is heavily propositional) |
| Lattice lemmas (`sup_comm`, `inf_comm`, `sup_le`, `le_sup_left`, `le_inf`, etc.) | `Set ∪/∩` are lattice `⊔/⊓`; lattice lemmas one-shot set identities |

### Per-world unlocks

| World | New tactics | New theorems/defs | Notes |
|-------|------------|-------------------|-------|
| W1 | `ext`, `specialize`, `change`, `show`, `unfold` | `Set.ext_iff`, `Set.Subset.antisymm` | `ext` is the dominant new tactic |
| W2 | `push_neg`, `rintro`, `left`, `right`, `rcases` | `Set.compl_def`, de Morgan | Enable `simp` (set lemmas only) midway through |
| W3 | — | Concrete set lemmas | May temporarily enable `norm_num`/`decide` for arithmetic |
| W4 | — | `Set.mem_iUnion`, `Set.mem_iInter`, `Set.mem_sUnion`, `Set.mem_sInter`, `Set.powerset`, `Set.mem_powerset_iff` | Powerset levels foreshadow Cantor (W22) |
| W5 | — | — (all prior available) | Pset: no new tools |
| W6 | `funext`, `congr` | `Function.Injective`, `.Surjective`, `.Bijective`, `.comp`, `.LeftInverse`, `.RightInverse` | — |
| W7 | — | Concrete ℕ/ℤ lemmas as needed | Example world |
| W8 | — | `Set.mem_image`, `Set.mem_preimage`, `Set.image_union`, `Set.preimage_inter`, `Set.range` | `obtain ⟨a, ha, rfl⟩` pattern taught |
| W9 | — | Concrete image/preimage lemmas as needed | Example world; may temporarily enable `norm_num`/`decide` |
| W10 | — | `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`, `Set.restrict`, `Set.inclusion` | — |
| W11 | — | — (all prior available) | Pset |
| W12 | `calc` | `Reflexive`, `Symmetric`, `Transitive`, `Antisymmetric` | PER introduced late in world |
| W13 | — | `Equivalence`, equivalence class defs, partition lemmas | — |
| W14 | — | Concrete ℤ lemmas, `Int.emod_emod_of_dvd` family as needed | May temporarily enable `omega` |
| W15 | — | — (all prior available) | Pset |
| W16 | — | `Setoid`, `Quotient`, `Quotient.mk`, `Quotient.lift`, `Quotient.ind`, `Quotient.sound`, `Quotient.exact` | `⟦·⟧` notation taught |
| W17 | — | Concrete quotient lemmas | — |
| W18 | — | `Equiv`, `Equiv.refl`, `.symm`, `.trans`, `.toFun`, `.invFun`, `.ofBijective`, `Equiv.Perm` | `≃` notation taught |
| W19 | — | — (all prior available) | Review/consolidation |
| W20 | — | `Subtype`, `Subtype.val`, `.property`, `.mk`, `Set.Elem` | `↥s`, `↑` coercion taught |
| W21 | — | `Fin`, `Bool` API as needed | May temporarily enable `omega`/`norm_num` |
| W22 | — | `Set.Countable`, `Countable`, `Set.Finite`, Cantor's theorem | — |
| W23 | — | `Encodable`, `Encodable.encode`, `.decode`, `Denumerable`, Schröder-Bernstein | — |
| W24 | — | — (all prior available) | Pset/consolidation |

### Exploit vectors requiring per-level `DisabledTactic` or `DisabledTheorem`

| Exploit | Why | Affected worlds |
|---------|-----|-----------------|
| `simp` (early) | Solves many set membership goals before learner learns the proof shape | W1 (fully disabled), W2 (enable midway) |
| `ext` (before W1) | Must be TAUGHT, not free from the start | W1 only: disabled until the teaching level |
| `norm_num` | Can solve arithmetic goals in concrete worlds | W3, W7, W14, W17, W21: enable only when needed |
| `omega` | Can solve ℕ/ℤ goals | W14, W21: enable only when needed |
| `fin_cases` | One-shots many goals on `Fin` | W21: disable if teaching Fin reasoning |
| `Set.subset_antisymm` | Should be earned in W1 boss, not free | W1: disabled until boss level |

## 7. Boss Map

| World | Boss description | Key moves integrated | Seeded by levels |
|-------|-----------------|---------------------|------------------|
| W1 | Prove `A ⊆ B → B ⊆ A → A = B` (double inclusion → equality) | ext, ↔, ⊆ specialization | W1:L1 (∈), W1:L3 (⊆), W1:L5 (ext) |
| W2 | Prove de Morgan: `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ` | ext, push_neg, ∩/∪ membership, complement | W2:L1 (∪), W2:L2 (∩), W2:L4 (ᶜ), W2:L5 (push_neg) |
| W3 | Multi-step set identity on concrete ℕ-sets | ext, membership chasing, concrete arithmetic | W3:L1–L6 (concrete membership/operations) |
| W4 | `A ∩ (⋃ i, f i) = ⋃ i, (A ∩ f i)` — intersection distributes over indexed union | ext, ⋃ membership (∃ i), ∩ membership, ∃ management | W4:L1 (⋃ mem), W4:L3 (⋂ mem), W4:L5 (combined) |
| W5 | Mixed problem: indexed + binary set ops in one proof | All set moves | W1–W4 (all) |
| W6 | Composition of bijections is bijective | unfold Bijective, inj∘inj, surj∘surj | W6:L3 (inj∘inj), W6:L5 (surj∘surj), W6:L7 (bijective = inj ∧ surj) |
| W7 | Verify specific function is bijective + construct inverse | Injectivity proof, surjectivity proof, inverse construction | W7:L1–L5 (concrete inj/surj), W6:L6 (inverse) |
| W8 | Injective image intersection: `f inj → f '' (A ∩ B) = f '' A ∩ f '' B` | ext, image membership (both directions), injectivity, ∩ | W8:L1 (image mem), W8:L3 (image ∪), W8:L5 (preimage ∩) |
| W9 | Concrete counterexample: `f '' (A ∩ B) ≠ f '' A ∩ f '' B` with specific f, A, B | image computation, counterexample construction, concrete membership | W9:L1 (concrete image), W9:L3 (concrete preimage), W8 (image membership pattern) |
| W10 | `InjOn s + SurjOn s t → BijOn s t` | InjOn def, SurjOn def, BijOn = InjOn ∧ SurjOn ∧ MapsTo | W10:L1 (MapsTo), W10:L3 (InjOn), W10:L5 (SurjOn) |
| W11 | Multi-step problem: image + injectivity + restriction | All function moves | W6–W10 (all) |
| W12 | PER reflexivity on domain: symmetric + transitive → `R x y → R x x` | symmetry, transitivity, PER, definition-unfolding | W12:L3 (symm), W12:L5 (trans), W12:L7 (PER) |
| W13 | Equivalence relation → partition (classes nonempty, disjoint, covering) | refl → nonempty, symm+trans → disjoint, class mem → covering | W13:L1 (equiv def), W13:L3 (class mem), W13:L5 (disjoint) |
| W14 | Verify non-trivial relation is equivalence + identify a class | refl/symm/trans verification, class computation | W14:L1–L3 (mod 2 verification), W14:L7 (class computation) |
| W15 | Mixed relation problem combining properties + equivalence | All relation moves | W12–W14 (all) |
| W16 | Lift function through quotient + prove property using Quotient.ind | Setoid construction, well-def proof, lift, ind | W16:L3 (well-def), W16:L5 (lift), W16:L7 (ind) |
| W17 | Lift operation on ℤ mod n + prove property | concrete well-def, concrete lift, concrete ind | W17:L1 (Setoid), W17:L3 (lift), W17:L5 (ind) |
| W18 | Construct Equiv from scratch + show toFun is bijective | Equiv.mk, left_inv, right_inv, bijective proof | W18:L2 (Equiv.mk), W18:L4 (left_inv), W18:L5 (right_inv) |
| W19 | Navigate between equality, equivalence, and Equiv in one proof | Quotient.sound, Equiv.ofBijective, all three notions | W13, W16, W18 (all) |
| W20 | Restrict function to subtype + prove preserved injectivity | Subtype.mk, val, property, coercion, injectivity | W20:L1 (mk), W20:L3 (val), W20:L5 (coercion) |
| W21 | Construct Equiv between concrete subtypes | Subtype construction, Equiv.mk, concrete arithmetic | W21:L1–L4 (concrete subtypes), W18 (Equiv) |
| W22 | Cantor's theorem (no surjection α → Set α) | diagonal set construction, contradiction, set membership | W22:L3 (diagonal intro), W22:L5 (contradiction setup), W22:L7 (diag application) |
| W23 | ℕ × ℕ is Encodable/Countable | encoding construction, product structure, injection/equiv | W23:L1 (Encodable def), W23:L3 (product encoding), W22 (countability) |
| W24 | Subtype countability + encoding integration | subtype construction, countability argument, encoding, Equiv | W20–W23 (all Cluster 5 material) |

## 8. Transfer and Retrieval Plan

### High-value move: Set extensionality

| Stage | World | What happens |
|-------|-------|-------------|
| First appearance | W1 | Introduced with `ext` tactic, full scaffolding, docstring explains the shape |
| Practiced with support | W2 | Used to prove set operation identities; `ext` is prompted in hints |
| Practiced with less support | W3, W4 | Used on concrete sets and indexed families; learner chooses when to apply |
| Fresh surface form | W8 | Applied to image/preimage equalities — same move, new notation context |
| Retrieval | W5, W11 | Pset worlds: learner must recognize when ext is the right move |
| Transfer | W19 | "In ordinary math: to show two sets are equal, show each element of one belongs to the other" |

### High-value move: Witness exhibition (∃)

| Stage | World | What happens |
|-------|-------|-------------|
| First appearance | W6 | Surjectivity proofs: given y, construct x with f(x) = y |
| Practiced with support | W7 | Concrete functions: the witness is a specific number |
| Fresh surface form | W8 | Image membership: to show y ∈ f '' S, find x ∈ S with f x = y |
| Concrete practice | W9 | Concrete image computations: the witness is a specific number in a specific set |
| More surface forms | W13 | Equivalence class nonemptiness; W16: quotient lift |
| Retrieval | W11, W15 | Pset worlds |
| Transfer | W19 | "To show something exists, find a specific thing and prove it works" |

### High-value move: Injectivity proof shape (assume f(a)=f(b), show a=b)

| Stage | World | What happens |
|-------|-------|-------------|
| First appearance | W6 | Abstract injectivity proofs |
| Practiced with support | W7 | Concrete functions: specific arithmetic |
| Fresh surface form | W8 | Image reasoning: extracting two preimages and using injectivity |
| Another surface form | W10 | InjOn: same shape but restricted to a set |
| Retrieval | W11 | Pset |
| Mirror image | W16 | Well-definedness is the "dual": assume a ~ b, show f(a) = f(b) |
| Transfer | — | "Injective: different inputs → different outputs. Prove by assuming equal outputs and deducing equal inputs." |

### High-value move: Well-definedness proof

| Stage | World | What happens |
|-------|-------|-------------|
| First appearance | W16 | Quotient.lift requires proving f respects the equivalence |
| Practiced with support | W16 | Multiple lift levels with increasing complexity |
| Concrete practice | W17 | Well-definedness for specific mod n functions |
| Retrieval | W19 | Used in the consolidation world |
| Transfer | — | "A map on a quotient must give the same answer for equivalent representatives" |

### High-value move: Diagonalization

| Stage | World | What happens |
|-------|-------|-------------|
| First appearance | W22 | Cantor's theorem: define s = {x \| x ∉ f x} |
| Preparation levels | W22 | Step-by-step: first construct s, then assume f is surj, then specialize to get contradiction |
| Boss | W22 | Full diagonalization in one proof |
| Transfer | — | "To show no function can cover everything, construct an object it must miss by using the function against itself" |

### High-value move: Constructing an Equiv

| Stage | World | What happens |
|-------|-------|-------------|
| First appearance | W18 | Equiv.mk with left_inv and right_inv proofs |
| Practiced with support | W18 | Multiple Equiv constructions with increasing difficulty |
| Concrete practice | W21 | Equiv between concrete subtypes / Fin types |
| Earlier seed | W6 | Inverse construction (without the Equiv wrapper) |
| Transfer | — | "An isomorphism is a pair of mutually inverse functions" |

## 9. Misconception Plan

| # | Misconception | Where addressed | Method |
|---|---------------|----------------|--------|
| 1 | "Sets are types" (`Set α` is `α → Prop`, not a type) | W1:L1 (intro docstring) + W20 (revisited when subtypes are actual types) | Explicit docstring in W1; in W20, the contrast becomes concrete: a subtype IS a type, a set is NOT |
| 2 | `f '' (A ∩ B) = f '' A ∩ f '' B` (false without injectivity) | W9 (counterexample level) + W8 (positive result with injectivity) | W9: construct specific f, A, B where equality fails (ConcreteImages world). W8 boss: prove it holds under injectivity |
| 3 | "Symmetric + transitive → reflexive" (false) | W14 (counterexample level) | Construct `fun (_ _ : ℕ) ↦ False`: symmetric (vacuous), transitive (vacuous), not reflexive |
| 4 | "Bijective = Equiv" | W18 (explicit comparison level) | Level where the learner has a bijection proof (Prop) and must construct an Equiv (data). The mismatch is the lesson. |
| 5 | "Quotient.lift just works" | W16 (early in the world) | Level where Quotient.lift is attempted and the well-definedness proof is the ONLY thing standing between the learner and success |
| 6 | "⊆ and ⊂ confusion" | W1 (docstring) | Warning in the intro when ⊆ is introduced; a note that ⊂ means strict |
| 7 | "Equivalence relation ≠ Equiv" | W19 (dedicated level) | Side-by-side: one is a property of a relation, the other is a data type. Different types, different purposes. |
| 8 | "Complement is ᶜ not - or ~" | W2 (notation teaching level) | Explicitly teach the notation; docstring warns about alternatives |
| 9 | "Image notation '' ≠ string quotes" | W8 (docstring) | Warning in the level that introduces `''` |
| 10 | "Countable includes finite" | W22 (explicit level) | Prove `Set.Finite → Set.Countable`. The level's docstring explicitly addresses this |
| 11 | "Antisymmetric ≠ not-symmetric" | W12 (docstring) + W14 (counterexample) | W12: docstring explains the distinction. W14: the identity relation is BOTH symmetric AND antisymmetric |
| 12 | "Set.restrict changes the codomain" | W10 (docstring warning) | Warning in the level that introduces restrict |
| 13 | "Image of a subset ≠ image restricted to a subset" | W10 (comparison level) | Level comparing `f '' s` with the range of `f ∘ Subtype.val` on `↥s` |

## 10. Major Risks

### Risk 1: Lattice alias exploits

**Severity**: High
**Description**: `Set α` with `∪/∩` forms a lattice. Every set identity (commutativity, associativity, de Morgan, distributive) has a lattice-level alias (`sup_comm`, `inf_comm`, `sup_le`, `le_sup_left`, etc.) that can one-shot the intended proof. This was a major exploit vector in the orders_lattices course.
**Mitigation**: Globally disable all lattice lemmas via `DisabledTheorem`. Maintain a running list of lattice aliases discovered during playtesting and add them to the disable list. Key candidates: `sup_comm`, `inf_comm`, `sup_le`, `le_sup_left`, `le_sup_right`, `le_inf`, `inf_le_left`, `inf_le_right`, `sup_inf_left`, `sup_inf_right`, `compl_sup`, `compl_inf`, `le_antisymm`.

### Risk 2: Set algebra drill redundancy

**Severity**: Medium
**Description**: Set identities (commutativity, associativity, de Morgan, distributive, absorption, double complement) all use the same proof shape: ext + case split + chase membership. After 4–5 such levels, additional ones teach nothing new.
**Mitigation**: Cap pure set-algebra levels at 5 per world. After the proof shape is learned, additional set identities should only appear if they introduce a new move (e.g., de Morgan requires push_neg; distribution over indexed union requires ∃ management).

### Risk 3: Quotient novelty overload (W16)

**Severity**: High
**Description**: W16 introduces Setoid, Quotient, Quotient.mk, ⟦·⟧ notation, Quotient.lift, well-definedness, Quotient.ind, and Quotient.sound — all in one world. This is a novelty hotspot.
**Mitigation**: Strict one-new-thing-per-level discipline. The level sequence in W16's spec above spreads these across 10+ levels. The world author must not compress this.

### Risk 4: Image/preimage notation confusion

**Severity**: Medium
**Description**: `''` (two single quotes for Set.image) and `⁻¹'` (superscript for Set.preimage) are non-obvious notation. Learners may confuse `''` with string quotes.
**Mitigation**: Dedicated notation introduction levels in W8 (first two levels are notation-only with trivial proofs). Docstring warnings. The proof move (exhibiting a preimage) is introduced AFTER the notation is familiar.

### Risk 5: Cantor's theorem difficulty

**Severity**: Medium
**Description**: The diagonalization argument is beautiful but requires several coordinated moves (define diagonal set, assume surjectivity, specialize, derive contradiction). As a single boss level, it may be too hard.
**Mitigation**: Break the argument into preparation levels. W22 should have at least 2–3 levels that practice individual steps of the diagonal argument before the boss assembles them. E.g., one level to construct the diagonal set, one level to derive the contradiction given the set, then the boss puts them together.

### Risk 6: Subtype coercion invisibility

**Severity**: Medium
**Description**: The `↥s` coercion and `↑` casts are often invisible in Lean's goal display. Learners may not realize they're working with a subtype until a tactic fails.
**Mitigation**: Explicit levels in W20 that teach the learner to recognize subtype coercions in goals. Docstrings that warn "if you see a type that looks like `↥s` or `{ x // P x }` in your goal, you're working with a subtype."

### Risk 7: Schröder-Bernstein complexity

**Severity**: Low
**Description**: The Schröder-Bernstein proof is long and uses fixed-point arguments. Proving it from scratch is beyond a basic course.
**Mitigation**: Use Schröder-Bernstein as a stated tool (available theorem), not a proved result. Learners apply it, not prove it. If the mathlib proof is accessible enough, one or two guided steps could be included, but this is optional.

### Risk 8: Concrete example formalization difficulty

**Severity**: Medium
**Description**: Some concrete examples (counterexample relations on small types, concrete image computations) may be surprisingly hard to formalize in Lean. Custom relations on `Fin 3` or specific set computations may require tactics that are disabled.
**Mitigation**: World authors should test concrete levels early. If a concrete example requires re-enabling disabled tactics (like `decide` or `norm_num`), do so for that specific level only with clear documentation.

## 11. Recommended First Three Worlds to Author

### 1. W1: SetsAndMembership

**Why first**: This is the foundation. Every later world depends on set membership and extensionality. It introduces `ext`, the most important tactic in the course, and establishes the proof pattern (ext → iff → chase) that the learner will use hundreds of times.

**Key authoring decisions**:
- How to introduce `Set α` as `α → Prop` without overwhelming the learner
- How many ⊆ levels before introducing ext
- Whether to use `Set.ext_iff` or the `ext` tactic as the primary teaching vehicle
- How to handle the `simp` disable gracefully (the learner may try it from NNG4 habit)

### 2. W2: SetOperations

**Why second**: Builds directly on W1 with the four main set operations. Introduces `push_neg` (new tactic), notation burden (∪, ∩, \, ᶜ), and the membership-chasing proof pattern.

**Key authoring decisions**:
- Level ordering: ∪ and ∩ first (symmetric), then \ and ᶜ (introduce negation)
- When to enable `simp` with set lemmas
- How many de Morgan / distributive law levels before diminishing returns
- Whether to introduce `rintro` here or wait

### 3. W3: ConcreteSets

**Why third**: Grounds the abstract set material in specific mathematical objects. The learner needs to see that evens, odds, and finite set operations are instances of what they just proved abstractly. This world also provides the first counterexamples.

**Key authoring decisions**:
- Which types to use: `ℕ`, `ℤ`, `Fin n`, or custom types
- How to handle arithmetic (enable `norm_num`/`omega` per-level? or keep disabled and use specific lemmas?)
- Balance between "verify membership in a specific set" levels and "compute a set operation" levels
- The strict-subset counterexample needs careful formalization
