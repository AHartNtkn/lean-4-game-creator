# Course Plan: Finite Mathematics

## 1. Course Promise

By the end of this course, the learner will be able to:
- Construct and reason about elements of `Fin n`, functions out of `Fin n`, and finite types
- Build, manipulate, and prove properties of `Finset`s including membership, operations, images, and cardinality
- Explain the List -> Multiset -> Finset abstraction ladder and why each layer exists
- Use `Fintype` to count elements of composite finite types
- Manipulate big operators (`∑`, `∏`) algebraically and prove identities by finset induction
- Work with factorials, binomial coefficients, powerset counting, and the binomial theorem
- Apply double counting, bijective proofs, and pigeonhole arguments
- Read and write formal proofs about finite objects with confidence that transfers to paper mathematics

## 2. Learner Profile

- **Prerequisites**: NNG4-level Lean fluency. The learner can use `rw`, `exact`, `apply`, `intro`, `cases`, `constructor`, `assumption`, `have`, `use`, and `induction` on natural numbers. They can read goal states and work in tactic mode.
- **What they do NOT know**: Subtypes and the `{ x // P x }` construction; typeclasses (`Fintype`); big operators (`∑`, `∏`); the `Finset` API; coercions (`↑`); `omega`; `ext`; function extensionality; `decide` in non-trivial contexts.
- **Mathematical background**: Comfortable with natural number arithmetic. No assumed familiarity with combinatorics, finite set theory, or formal counting arguments.

## 3. Granularity Plan

### Macro (course)
The course has 7 phases, 29 worlds. Each phase builds on the previous and adds one major conceptual layer.

### Meso (world)
Each world covers one theorem family, one proof-move cluster, or one concrete object family. The world introduction states the world's center of gravity. The boss integrates the world's main moves.

### Micro (level)
Each level isolates one dominant lesson. The novelty budget is strict: at most one new burden per level (new math, new proof move, new Lean tactic, OR new notation). Everything else should be familiar enough to be automatic.

## 4. World Graph

---

### Phase 1: Finite Types (Worlds 1-4)

---

#### W01: MeetFin (Onboarding/Lecture)

**Type**: Onboarding + Lecture hybrid

**Promise**: By the end of this world, the learner will be able to construct elements of `Fin n`, extract their natural number values, and reason about the boundary cases `Fin 0`, `Fin 1`, and `Fin 2`.

**Theorem families**:
- `Fin.mk` / anonymous constructor `⟨k, hk⟩`
- `Fin.val` / coercion `↑i`
- `Fin.ext_iff` / `Fin.ext`
- `Fin 0` (empty), `Fin 1` (unique/unit), `Fin 2` (Bool-like)

**Proof-move goals**:
- Construct an element of `Fin n` by providing a natural number and a proof it's less than `n`
- Extract the ℕ value from a `Fin n` element
- Prove two `Fin n` elements are equal by showing their values are equal
- Reason about empty types (`Fin 0`) and unique elements (`Fin 1`)

**Inventory changes**:
- `NewTactic omega` — needed for `Fin` arithmetic goals (e.g., proving `k < n`)
- `NewDefinition Fin Fin.val Fin.mk`
- `TheoremTab "Fin"`
- `NewTheorem Fin.ext_iff`

**Level sketch**:
- L01: What is `Fin n`? Construct an element of `Fin 5` using `⟨k, hk⟩`. Lesson: anonymous constructor for subtypes.
- L02: `Fin.val` and coercion. Given `i : Fin 5`, prove a fact about `↑i`. Lesson: extracting the ℕ value.
- L03: Two elements of `Fin n` are equal iff their values are. Use `Fin.ext_iff`. Lesson: extensionality for Fin.
- L04: `Fin 0` has no elements. Prove a goal about `Fin 0` using `Fin.elim0` or similar. Lesson: empty type reasoning. Warning: `Fin n` elements start at 0.
- L05: `Fin 1` has exactly one element. Prove `∀ x : Fin 1, x = 0`. Lesson: unique element.
- L06: `Fin 2` has two elements. Case-split on `Fin 2` manually. Lesson: exhaustive case analysis.
- L07 (Boss): Prove a statement requiring element construction, value extraction, and extensionality. Integration of L01-L06 moves.

**Misconceptions addressed**: `Fin n` starts at 0 (not 1); `↑i` vs `i.val` (same thing, different notation); `Fin 0` is empty (surprising).

**Dependencies**: None (first world)

**Pset partner**: PsetFin (W04)

---

#### W02: FinNavigation (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to navigate within `Fin n` using `Fin.succ`, `Fin.castSucc`, and `Fin.last`, and perform case analysis on small `Fin` types.

**Theorem families**:
- `Fin.succ`, `Fin.castSucc`, `Fin.last`
- `Fin.succ_val`, `Fin.castSucc_val`, `Fin.last_val`
- `Fin.val_succ`, `Fin.val_castSucc`
- Case analysis: manual case split on `Fin n` for small `n`

**Proof-move goals**:
- Use `Fin.succ` to move forward in `Fin (n+1)`
- Use `Fin.castSucc` to embed `Fin n` into `Fin (n+1)`
- Use `Fin.last` to access the final element
- Perform exhaustive case analysis on `Fin 3`, `Fin 4`

**Inventory changes**:
- `NewDefinition Fin.succ Fin.castSucc Fin.last`
- `NewTheorem Fin.val_succ Fin.castSucc_val Fin.last_val`
- `DisabledTactic fin_cases` — force manual case analysis while teaching the concept

**Level sketch**:
- L01: `Fin.last n` — what is the last element? Lesson: accessing boundary.
- L02: `Fin.castSucc` — embed into a larger type. Lesson: weakening the bound.
- L03: `Fin.succ` — the successor in `Fin`. Lesson: moving forward.
- L04: Relationship between `succ`, `castSucc`, and `last`. Lesson: how navigation fits together.
- L05: Manual case analysis on `Fin 3`. Lesson: enumerating all elements.
- L06: Case analysis on `Fin 4` — longer but same shape. Lesson: the pattern scales.
- L07 (Boss): Prove a statement about `Fin (n+1)` that requires using `last`, `castSucc`, and case analysis together.

**Dependencies**: MeetFin

**Pset partner**: PsetFin (W04)

---

#### W03: FinTuples (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand that `Fin n -> α` is a "tuple" (ordered list of fixed length), and will be able to construct and decompose tuples using `Fin.cons` and `Fin.snoc`.

**Theorem families**:
- `Fin.cons` — prepend an element to a tuple
- `Fin.snoc` — append an element to a tuple
- `Fin.tail` — drop the first element
- `Fin.cons_zero`, `Fin.cons_succ`
- `Fin.snoc_last`, `Fin.snoc_castSucc`
- Function extensionality for `Fin n -> α`

**Proof-move goals**:
- Build a function `Fin n -> α` by specifying each value
- Use `Fin.cons` to build tuples recursively
- Decompose a tuple using `Fin.tail`
- Prove two tuples are equal by proving they agree at every index (function extensionality)

**Inventory changes**:
- `NewDefinition Fin.cons Fin.snoc Fin.tail`
- `NewTheorem Fin.cons_zero Fin.cons_succ Fin.snoc_last Fin.snoc_castSucc`
- `NewTactic funext` — function extensionality (new tactic)

**Level sketch**:
- L01: `Fin n -> α` IS a tuple. Define a function `Fin 3 -> ℕ` by cases. Lesson: functions from Fin as data.
- L02: `Fin.cons` — build a tuple by prepending. Lesson: recursive tuple construction.
- L03: `Fin.cons_zero` and `Fin.cons_succ` — access elements of a `cons`-built tuple. Lesson: destructor lemmas.
- L04: `Fin.snoc` — build a tuple by appending. Lesson: alternative construction.
- L05: `Fin.tail` — drop the first element. Lesson: tuple decomposition.
- L06: Function extensionality (`funext`). Prove two tuples are equal by proving pointwise equality. Lesson: ext for functions.
- L07 (Boss): Build a tuple, decompose it, and prove an equality. Requires `cons`, access lemmas, and `funext`.

**Dependencies**: FinNavigation

**Pset partner**: PsetFin (W04)

---

#### W04: PsetFin (Problem Set)

**Type**: Pset

**Promise**: The learner retrieves and transfers Fin skills on fresh problems without scaffolding.

**Proof-move goals**:
- Unsupported retrieval of element construction, navigation, and tuple manipulation
- Transfer to fresh surface forms not seen in W01-W03

**Inventory changes**: `obtain` introduced (standard Lean idiom for existential destructuring, previewed in MeetFin L16).

**Level sketch**:
- L01: Two-witness existential with sum constraint (retrieval of W01).
- L02: Abstract castSucc/last separation for general n (transfer from W02).
- L03: Formula-based snoc reconstruction (retrieval of W03).
- L04: Antisymmetric equality from two inequalities (transfer).
- L05: Formula-to-tuple identification with val lemma (integration of W01-W03).
- L06: Vacuous truth over Fin 0 (retrieval of W01).
- L07: Abstract succ/zero separation for general n (transfer from W02).
- L08: Existential destructuring with obtain (new tactic introduction).
- L09: Applied 0/succ decomposition (retrieval from W02).
- L10: Modular function equality (integration).
- L11: General castSucc/last decomposition for all n (concrete-to-abstract generalization).
- L12: Cyclic permutation has no fixed points (application/transfer).
- L13: Concrete pigeonhole: f : Fin 3 -> Fin 2 has a collision (theorem-proving).
- L14 (Boss): Reconstruction + comparison + non-constant witness. 6+ integrated moves.

**Dependencies**: MeetFin, FinNavigation, FinTuples

---

### Phase 2: Finite Sets (Worlds 5-8)

---

#### W05: FinsetBasics (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand `Finset α` as a finite set with decidable equality, and will be able to construct finsets using `∅`, `singleton`, `insert`, and `Finset.range`, and prove membership facts.

**Theorem families**:
- `Finset.mem_empty`, `Finset.not_mem_empty`
- `Finset.mem_singleton`
- `Finset.mem_insert`
- `Finset.mem_range`
- `{a, b, c}` literal notation = nested `insert`

**Proof-move goals**:
- Prove `x ∈ s` by construction (showing which insert/singleton it came from)
- Prove `x ∉ s` (e.g., `x ∉ ∅`)
- Understand `{a, b, c}` as `insert a (insert b {c})`
- Work with `Finset.range n` = `{0, ..., n-1}`

**Inventory changes**:
- `NewDefinition Finset Finset.empty Finset.singleton Finset.insert Finset.range`
- `NewTactic decide` — re-enabled in L12 after manual techniques are taught; disabled on L01-L11 to force manual membership reasoning
- `TheoremTab "Finset"`
- `NewTheorem Finset.mem_empty Finset.not_mem_empty Finset.mem_singleton Finset.mem_insert Finset.mem_range`
- `NewDefinition Finset.Nonempty`
- `NewTheorem Finset.Nonempty.some_mem`
- Disable: `norm_num` (force manual membership reasoning)

**Level sketch** (plan: 9 levels, implemented: 18 levels):
- L01-L08: Core membership lemmas (mem_insert, mem_singleton, mem_empty, mem_range, literal notation, insert idempotency, Nonempty)
- L09-L17: Extended practice including non-membership proofs, range boundary cases, filter membership, insert_eq_of_mem, multiple range levels
- L18 (Boss): 5-part membership integration
- Note: Expanded from 9 to 18 levels during implementation to give more practice with membership peeling before moving to operations.

**Misconceptions addressed**: `Finset.range n` is `{0,...,n-1}` not `{0,...,n}`; `insert` is idempotent; `{a,b,c}` is sugar for nested inserts.

**Dependencies**: FinTuples (knows `Fin`, subtypes)

**Pset partner**: PsetFinset (W08)

---

#### W06: FinsetOperations (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to use union, intersection, set difference, filter, and subset on finsets, and prove finset equality by extensionality.

**Theorem families**:
- `Finset.mem_union`, `Finset.mem_inter`, `Finset.mem_sdiff`
- `Finset.mem_filter`
- `Finset.subset_iff`, `Finset.Subset`
- `Finset.ext_iff` / `Finset.ext`

**Proof-move goals**:
- Prove membership in `s ∪ t`, `s ∩ t`, `s \ t`, `s.filter p`
- Prove `s ⊆ t` by showing `∀ x ∈ s, x ∈ t`
- Prove `s = t` by extensionality (`ext`)
- Prove `s = t` by mutual containment (`⊆` + `⊇`)

**Inventory changes**:
- `NewTactic ext simp_only` — introduce extensionality tactic; `simp only` for targeted Finset simplification
- `NewDefinition Finset.union Finset.inter Finset.sdiff Finset.filter`
- `NewTheorem Finset.mem_union Finset.mem_inter Finset.mem_sdiff Finset.mem_filter Finset.subset_iff Finset.ext_iff`
- Disable: All lattice aliases (`sup_comm`, `inf_comm`, `inf_le_left`, `sup_le`, `le_antisymm`, `sup_eq_left`, etc.) — these are exploit vectors
- Disable: `ext` on the level that introduces it (force discovery of why `ext` is needed first)

**Level sketch** (plan: 10 levels, implemented: 25 levels):
- L01-L04: Core operations (mem_union, mem_inter, mem_sdiff, mem_filter)
- L05-L08: Subset, ext, mutual containment, lattice notation warning
- L09-L11: simp only, intersection identity, disjoint detection
- L12-L15: Identity proofs (idempotency, commutativity, associativity) — marked as optional skip for experienced learners
- L16-L17: Lattice notation practice, simp only identity
- L18-L20: De Morgan's laws, by_contra introduction, complement patterns
- L21-L24: Partition, absorption, distributivity (2 variants)
- L25 (Boss): De Morgan second law requiring nested by_contra
- Note: Expanded from 10 to 25 levels to cover the full ext+unfold+logic recipe with comprehensive identity practice.

**Misconceptions addressed**: `∪`/`∩` are lattice `⊔`/`⊓` underneath — goal state may show lattice notation.

**Dependencies**: FinsetBasics

**Pset partner**: PsetFinset (W08)

---

#### W07: FinsetImage (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to use `Finset.image` and understand the relationship between injectivity and cardinality of images.

**Theorem families**:
- `Finset.mem_image`
- `Finset.image_empty`, `Finset.image_singleton`, `Finset.image_insert`
- `Finset.card_image_le`
- `Finset.card_image_of_injOn` / `Finset.card_image_of_injective`
- `Finset.map` — **deferred to a dedicated Embeddings world (not W10)**. `Finset.map` requires embeddings (`α ↪ β`), which are a bundled-morphism concept that adds too much novelty to fit into AbstractionLadder alongside the List→Multiset→Finset ladder. W07 mentions `map` in L13's conclusion for awareness. W10 mentions `map_eq_image` in the boss conclusion for awareness. The `map_eq_image` bridge and formal embedding work will be covered in a later world.

**Proof-move goals**:
- Prove `y ∈ Finset.image f s` by providing a witness `x ∈ s` with `f x = y`
- Prove that image can shrink cardinality (non-injective maps)
- Prove that injective maps preserve cardinality
- Prove image distributes over intersection under injectivity

**Inventory changes**:
- `NewDefinition Finset.image`
- `NewTheorem Finset.mem_image Finset.card_image_le Finset.card_image_of_injective`
- `DisabledTactic norm_num` — force manual reasoning about cardinality

**Level sketch** (plan: 7 levels, implemented: 23 levels):
- L01-L02: Forward image membership (witness construction)
- L03-L08: Backward image extraction, non-membership proofs, subset via image
- L09-L11: Image algebra (union distribution, intersection subset, counterexample)
- L12-L14: Cardinality bounds (card_image_le, card_image_of_injective, card_image_iff)
- L15-L18: Image and injectivity interactions, injective function proofs
- L19-L20: Filter interaction, singleton image
- L21: Counting proves injectivity (native_decide, backward rewrite with ←)
- L22: show tactic for injectivity proofs
- L23 (Boss): 4-part integration (forward membership, subset bound, card bounds, injectivity)
- Note: Expanded from 7 to 23 levels to thoroughly cover all four move families (forward, backward, cardinality, algebra).

**Misconceptions addressed**: `Finset.image` can shrink cardinality — injectivity is not free.

**Dependencies**: FinsetOperations

**Pset partner**: PsetFinset (W08)

---

#### W08: PsetFinset (Problem Set)

**Type**: Pset

**Promise**: The learner retrieves Finset skills on fresh problems without scaffolding.

**Proof-move goals**:
- Unsupported retrieval of membership, operations, extensionality, image
- Transfer to fresh surface forms

**Inventory changes**: None new.

**Level sketch** (plan: 6 levels, implemented: 14 levels):
- L01: Compound membership (filter + intersection + insert)
- L02: Double complement under subset (ext + by_contra)
- L03: Filter preserves containment (filter + intersection + subset)
- L04: Union and intersection subset (union + inter + cases)
- L05: Union complement (sdiff + union + cases + absurd)
- L06: Image of nonempty set (obtain + forward image)
- L07: Injective non-membership (backward extraction + injectivity + contradiction)
- L08: Filter image containment (filter + backward/forward image)
- L09: Cardinality of injective image (card_image_of_injective + card_range)
- L10: Image, union, and set difference integration (6 integrated moves)
- L11: De Morgan subset direction (sdiff + union + inter + negation)
- L12: Image monotonicity (subset → image subset)
- L13: Non-membership from image non-membership (contrapositive + forward image)
- L14 (Boss): Image preserves set difference under injectivity (7+ integrated moves)
- Note: Expanded from 6 to 14 levels for adequate retrieval coverage of 3 lecture worlds.

**Dependencies**: FinsetBasics, FinsetOperations, FinsetImage

---

### Phase 3: Cardinality and Structure (Worlds 9-13)

---

#### W09: Cardinality (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to compute cardinalities of finsets using the card_* lemma family, and prove inclusion-exclusion for two sets.

**Theorem families**:
- `Finset.card_empty`, `Finset.card_singleton`
- `Finset.card_insert_of_not_mem`, `Finset.card_erase_of_mem`
- `Finset.card_range`
- `Finset.card_mono` (monotonicity: `s ⊆ t -> card s ≤ card t`)
- `Finset.card_union_add_card_inter` (inclusion-exclusion)
- `Finset.card_sdiff_add_card_inter` (sdiff + inter)
- `Finset.card_product` (|s ×ˢ t| = |s| * |t|)

**Proof-move goals**:
- Compute card of a finset built by empty/singleton/insert
- Use card_mono for subset-based bounds
- Apply inclusion-exclusion: |s ∪ t| + |s ∩ t| = |s| + |t|
- Use card_product for product cardinality
- Prove equality by showing ≤ in both directions (antisymmetry for ℕ)

**Inventory changes**:
- `NewDefinition Finset.card`
- `NewTheorem Finset.card_empty Finset.card_singleton Finset.card_insert_of_not_mem Finset.card_mono Finset.card_union_add_card_inter Finset.card_product`
- `norm_num` stays disabled — `omega` suffices for all cardinality arithmetic
- `TheoremTab "Card"`

**Level sketch** (plan: 9 levels, implemented: 24 levels):
- L01-L05: Core card lemmas (card_empty, card_singleton, nonempty bridge, nonempty from card, card_eq_zero)
- L06-L09: Building card (card_insert, insert idempotency, concrete card computation, card_range)
- L10-L12: Comparing (card_erase, card_le_card/subsets, card_filter_le)
- L13-L16: Combining (inclusion-exclusion, disjoint union, complement counting, multiplication principle)
- L17-L18: Finset.univ (card_univ, card_fin, subset_univ)
- L19: Concrete univ verification (Finset.univ for Fin 3 = {0,1,2})
- L20: Abstract pigeonhole for Fin 3 -> Fin 2
- L21: General pigeonhole for Fin (n+2) -> Fin (n+1)
- L22: Capstone — injective implies surjective (image = univ)
- L23: Converse — surjective implies image = univ
- L24 (Boss): Chain four card lemmas in one proof (sdiff, monotonicity, erase, inclusion-exclusion)
- Note: Expanded from 9 to 24 levels to cover the full card toolkit plus pigeonhole and the injective-surjective equivalence.

**Dependencies**: FinsetImage (needs card_image_le from W07)

**Pset partner**: PsetCardinality (W13)

---

#### W10: AbstractionLadder (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand the three-layer abstraction: `List α` (ordered, with duplicates) -> `Multiset α` (unordered, with duplicates) -> `Finset α` (unordered, no duplicates), and why each layer exists.

**Theorem families**:
- `List.length`, `List.mem`, `List.append`
- `List.Perm` — permutation relation
- `List.Nodup`
- `Multiset.card`, `Multiset.count`
- `List.toFinset`, `Multiset.toFinset`
- Relationship: `Finset.val` gives the underlying `Multiset`

**Proof-move goals**:
- Work with basic list operations
- Prove two lists are permutations
- Show that `Nodup` connects lists to finsets
- Show what each quotient forgets (order, then duplicates)
- Convert between layers

**Inventory changes**:
- `NewDefinition List Multiset List.Perm List.Nodup`
- `NewTheorem List.length_append Multiset.card_cons List.Perm.length_eq`
- `TheoremTab "List" "Multiset"`

**Level sketch**:
- L01: Lists: `[1, 2, 3]` has length 3, `1 ∈ [1, 2, 3]`. Lesson: basic list operations.
- L02: Lists are ordered: `[1, 2, 3] ≠ [3, 1, 2]`. Lesson: order matters for equality.
- L03: `List.Perm` — `[1, 2, 3] ~ [3, 1, 2]`. Lesson: permutation ignores order.
- L04: `Multiset` — quotient of `List` by `Perm`. `{1, 2, 3} = {3, 1, 2}` as multisets. Lesson: order forgotten.
- L05: Multisets keep duplicates: `Multiset.count 2 {1, 2, 2, 3} = 2`. Lesson: multiplicity matters.
- L06: `List.Nodup` — a list with no duplicates. `[1, 2, 3].Nodup` but not `[1, 2, 2, 3].Nodup`. Lesson: the bridge to finsets.
- L07: `List.toFinset` / `Multiset.toFinset` — how to get from lists/multisets to finsets. Lesson: the quotient forgets duplicates.
- L08: Contrast: `[1, 2, 2, 3]` as list (length 4), as multiset (card 4), as finset (card 3). Lesson: the full picture.
- L09 (Boss): A proof that requires understanding which layer to work in and converting between them. E.g., prove a fact about `List.toFinset` that requires reasoning about `Nodup` and `Perm`.

**Misconceptions addressed**: List ≠ Multiset (order matters); Multiset ≠ Finset (duplicates matter); the three types have different `card`/`length`.

**Dependencies**: Cardinality

**Pset partner**: PsetCardinality (W13)

---

#### W11: Fintype (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand `Fintype α` as a typeclass asserting that `α` has finitely many elements, and will be able to use `Finset.univ`, `Fintype.card`, and the composition instances.

**World intro note**: The introduction text must include a clear warning that not every type is finite: `ℕ` has no `Fintype` instance. Attempting `Fintype.card ℕ` is a type error. This is a core misconception — learners who have only worked with `Fin n` may assume finiteness is universal.

**Theorem families**:
- `Fintype.card`, `Fintype.elems`
- `Finset.univ` — the finset of all elements
- `Finset.mem_univ` — everything is in `univ`
- `Fintype.card_fin` — `Fintype.card (Fin n) = n`
- `Fintype.card_prod` — `card (α × β) = card α * card β`
- `Fintype.card_sum` — `card (α ⊕ β) = card α + card β`
- `Fintype.card_fun` — `card (α -> β) = card β ^ card α`
- `Fintype.card_congr` — `α ≃ β -> card α = card β` (first bijective counting)

**Proof-move goals**:
- Use `Finset.univ` and `mem_univ` to access all elements
- Compute `Fintype.card` for built-in types (`Fin n`, `Bool`, `Unit`)
- Use composition instances: products, sums, subtypes
- Use `Fintype.card_congr` for bijective counting (first Equiv-based proof)
- Understand that `ℕ` is NOT a `Fintype` — not every type is finite

**Inventory changes**:
- `NewDefinition Fintype Finset.univ Fintype.card`
- `NewTheorem Finset.mem_univ Fintype.card_fin Fintype.card_prod Fintype.card_sum Fintype.card_fun Fintype.card_congr`
- `TheoremTab "Fintype"`

**Level sketch**:
- L01: `Fintype (Fin n)` — `Fin n` is finite. `Fintype.card (Fin n) = n`. Lesson: the card theorem.
- L02: `Finset.univ` — the set of all elements. `∀ x : Fin n, x ∈ Finset.univ`. Lesson: `mem_univ`.
- L03: `Fintype Bool` — `Fintype.card Bool = 2`. Lesson: other finite types.
- L04: Products are finite — `card (Fin 2 × Fin 3) = 6`. Lesson: `card_prod`.
- L05: Sums are finite — `card (Fin 2 ⊕ Fin 3) = 5`. Lesson: `card_sum`.
- L06: Function types — `card (Fin 2 -> Fin 3) = 9`. Lesson: `card_fun` = m^n.
- L07: ℕ is NOT finite — `ℕ` has no `Fintype` instance. Show that attempting `Fintype.card ℕ` fails. Lesson: finiteness is a property, not a given. Warning: not every type you know is finite.
- L08: `Fintype.card_congr` — if `α ≃ β` then `card α = card β`. Lesson: bijective counting. This is the first Equiv-based argument.
- L09 (Boss): Compute the cardinality of a composite type (e.g., `Fin 2 × Fin 3 -> Bool`) using multiple card_* lemmas.

**Misconceptions addressed**: `ℕ` has no `Fintype` instance — not every type is finite.

**Dependencies**: AbstractionLadder

**Pset partner**: PsetCardinality (W13)

---

#### W12: CountingTypes (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will have computed cardinalities of several concrete finite types and connected abstract card_* theorems to concrete numbers.

**Object**: Concrete finite types built from `Fin`, `Bool`, products, sums, and function types.

**Proof-move goals**:
- Apply `Fintype.card_*` to concrete types and simplify to numbers
- Build an `Equiv` between two concrete types and use `card_congr`
- See `Fintype.card_fun` in action: count functions `Fin n -> Fin m`
- See `Fintype.card_pi` in action: count dependent functions

**Inventory changes**:
- `NewDefinition Nat.descFactorial`
- `NewTheorem Nat.descFactorial_zero Nat.descFactorial_succ`

**Level sketch**:
- L01: `card (Fin 2 -> Bool) = 4`. Direct computation. Concretization.
- L02: `card (Fin 3 -> Fin 2) = 8 = 2^3`. Functions as assignments. Concretization.
- L03: `card (Fin 2 × Fin 2) = card (Fin 4)`. Build an equivalence. First Equiv construction.
- L04: Counting subsets: `card (Fin n -> Bool) = 2^n` — functions to `Bool` are subsets. Motivation for powerset counting.
- L05: Introduce `Nat.descFactorial` — the falling factorial `n * (n-1) * ... * (n-k+1)`. Count injections `Fin k ↪ Fin n` for small k, n. Connection to `Nat.descFactorial`.
- L06: Inclusion-exclusion practice — compute `card (A ∪ B)` for concrete finsets `A` and `B` where `A ∩ B` is nonempty. Apply `card_union_add_card_inter` from W09 in a Fintype/counting context. Lesson: scaffolded retrieval of inclusion-exclusion on fresh surface.
- L07 (Boss): Compute the cardinality of a non-trivial composite type using card_prod, card_fun, and/or card_congr.

**Dependencies**: Fintype

**Pset partner**: PsetCardinality (W13)

---

#### W13: PsetCardinality (Problem Set)

**Type**: Pset

**Promise**: The learner retrieves cardinality, abstraction ladder, and Fintype skills on fresh problems.

**Proof-move goals**:
- Unsupported retrieval of card_* lemmas, ext, inclusion-exclusion
- Transfer of Fintype.card to new type constructions
- Integration across W09-W12

**Level sketch** (11 levels):
- L01: Complement + erase combined (retrieval W09: card_sdiff_add_card_inter, card_erase_of_mem).
- L02: Subset bound via inclusion-exclusion + monotonicity (transfer W09).
- L03: Converse inclusion-exclusion — compute |s ∩ t| from |s ∪ t|, |s|, |t| (transfer W09).
- L04: Triple disjoint union — iterated card_union_of_disjoint (retrieval W09).
- L05: List→Finset bridge with card_insert (cross-world W09+W10).
- L06: Multiset cardinality — card_cons + coe_card retrieval (retrieval W10).
- L07: ext recognition — same elements implies same card (retrieval W06+W09).
- L08: Function type cardinality with abstract domain (transfer W11).
- L09: Subtype complement with equivalence decomposition (transfer W11).
- L10: Injection counting with abstract domain (cross-world W11+W12).
- L11 (Boss): Four-world integration — inclusion-exclusion + nodup bridge + equivalence + falling factorial. 12+ tactic steps.

**Dependencies**: Cardinality, AbstractionLadder, Fintype, CountingTypes

---

### Phase 4: Big Operators (Worlds 14-18)

---

#### W14: BigOpIntro (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand `∑ x ∈ s, f x` and `∏ x ∈ s, f x`, know the constructor lemmas for empty/singleton/insert, and be able to unfold sums over small concrete finsets.

**Theorem families**:
- `Finset.sum_empty`, `Finset.prod_empty`
- `Finset.sum_singleton`, `Finset.prod_singleton`
- `Finset.sum_insert`, `Finset.prod_insert`
- `Finset.sum_congr`, `Finset.prod_congr`

**Proof-move goals**:
- Read and write `∑ x ∈ s, f x` notation
- Unfold a sum/product over a small finset to individual terms
- Use `sum_insert` to peel off one element
- Use `sum_congr` to rewrite the summand

**Inventory changes**:
- `NewDefinition Finset.sum Finset.prod`
- `NewTheorem Finset.sum_empty Finset.sum_singleton Finset.sum_insert Finset.sum_congr Finset.prod_empty Finset.prod_singleton Finset.prod_insert Finset.prod_congr`
- `TheoremTab "BigOp"`
- Disable: `norm_num` on early levels (force manual sum unfolding)

**Level sketch**:
- L01: Notation — what does `∑ x ∈ s, f x` mean? Read the goal state. Lesson: big-operator notation.
- L02: `sum_empty` — `∑ x ∈ ∅, f x = 0`. Lesson: base case is 0 (not undefined!). Warning: empty sum = additive identity.
- L03: `sum_singleton` — `∑ x ∈ {a}, f x = f a`. Lesson: sum over singleton.
- L04: `sum_insert` — `a ∉ s -> ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x`. Lesson: peeling off one element.
- L05: Unfold `∑ x ∈ {1, 2, 3}, f x` completely using repeated `sum_insert`. Lesson: concrete computation.
- L06: `prod_empty`, `prod_singleton`, `prod_insert` — same story for products. Lesson: multiplicative analogues. Warning: empty product = 1.
- L07: `sum_congr` — rewrite the summand pointwise. Lesson: rewriting under a binder.
- L08: Connection to the abstraction ladder — `Finset.sum` is defined via `Multiset.sum`, which is defined via `List.sum`. Show that `∑ x ∈ s, f x` ultimately reduces through the Multiset layer. Lesson: retrieval of the List → Multiset → Finset pipeline from W10 in a new context. This is why the abstraction ladder matters — big operators sit on top of it.
- L09 (Boss): Compute a sum over a specific finset by unfolding with `sum_insert`, rewriting with `sum_congr`, and simplifying. Integration of all constructor lemmas.

**Misconceptions addressed**: Sum over empty set is 0, not undefined; product over empty set is 1.

**Dependencies**: FinsetOperations (needs membership, insert)

**Pset partner**: PsetBigOp (W18)

---

#### W15: BigOpAlgebra (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to manipulate big operators algebraically: splitting sums, filtering, constant sums, and distributivity.

**Theorem families**:
- `Finset.sum_union` (disjoint case)
- `Finset.sum_filter`
- `Finset.sum_const`
- `Finset.sum_add_distrib`
- `Finset.prod_mul_distrib`
- `Finset.sum_comm` (double sum interchange)

**Proof-move goals**:
- Split a sum by disjoint union
- Filter a sum by a predicate
- Simplify constant sums: `∑ x ∈ s, c = card s * c`
- Distribute addition inside sums / multiplication inside products
- Interchange order of double summation

**Inventory changes**:
- `NewTactic calc ring ring_nf` — introduce calc blocks for chained equalities; `ring`/`ring_nf` for algebraic simplification in sum manipulation
- `NewTheorem Finset.sum_union Finset.sum_filter Finset.sum_const Finset.sum_add_distrib Finset.prod_mul_distrib Finset.sum_comm`

**Level sketch**:
- L01: `sum_union` — split a sum over a disjoint union. Lesson: decomposition by partition.
- L02: `sum_filter` — filter the summation set. Lesson: conditional sums.
- L03: `sum_const` — `∑ x ∈ s, c = card s * c`. Lesson: constant sums.
- L04: `sum_add_distrib` — `∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x`. Lesson: linearity of sums.
- L05: `prod_mul_distrib` — multiplicative analogue. Lesson: products distribute.
- L06: `sum_comm` — interchange `∑ x, ∑ y, f x y = ∑ y, ∑ x, f x y`. Lesson: double sums.
- L07: Rewriting under binders with `sum_congr rfl (fun x hx => ...)`. Lesson: targeted rewriting inside ∑.
- L08: `calc` blocks for multi-step sum manipulation. Chain equalities: `∑ x ∈ s, f x = ... = ... = result` using `calc`. Lesson: `calc` blocks organize multi-step rewrites into readable chains. This is a core Lean skill for algebraic proofs.
- L09: `ring` and `ring_nf` — use `ring` to close algebraic goals and `ring_nf` to normalize ring expressions during sum manipulation. Lesson: `ring` automates the algebra once you've reduced a sum to a pure arithmetic/algebraic expression. Warning: `ring` only works on ring goals (no hypotheses, no membership), so it complements rather than replaces the sum_* lemmas.
- L10 (Boss): Prove an algebraic identity for sums requiring decomposition, distributivity, constant-sum simplification, and `calc`/`ring`. Multiple algebraic moves integrated.

**Dependencies**: BigOpIntro

**Pset partner**: PsetBigOp (W18)

---

#### W16: FinsetInduction (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to prove big-operator identities by induction on finsets, using `Finset.induction_on` with base case `∅` and inductive step `insert a s` where `a ∉ s`.

**Theorem families**:
- `Finset.induction_on`
- Pattern: base case (use `sum_empty`), inductive step (use `sum_insert`, rewrite, apply IH)
- Note: `Finset.cons_induction` was removed — it's a minor variant of `induction_on` (uses `cons` instead of `insert`) with the same proof strategy. Teaching it as a separate level adds complexity without pedagogical payoff.

**Proof-move goals**:
- Set up finset induction (different from ℕ induction)
- Handle the base case `∅` using `sum_empty`/`prod_empty`
- Handle the inductive step: given `a ∉ s` and the IH for `s`, prove for `insert a s`
- Use `sum_insert` in the inductive step
- Apply the induction hypothesis and finish with arithmetic

**Inventory changes**:
- `NewTheorem Finset.induction_on`
- `NewTactic induction` — extend to finset induction (same tactic, new context)

**Level sketch**:
- L01: Finset induction setup — see the induction hypothesis shape. Lesson: how finset induction differs from ℕ induction. The hypothesis `a ∉ s` is new.
- L02: Base case practice. Prove a sum identity for `∅`. Lesson: base case is always `sum_empty`.
- L03: Inductive step practice. Given IH, prove for `insert a s`. Lesson: use `sum_insert`, rewrite, apply IH.
- L04: Full induction proof for a simple identity (e.g., `∑ x ∈ s, 1 = card s`). Lesson: the complete pattern.
- L05: A slightly harder induction proof (e.g., `∑ x ∈ s, 2 * f x = 2 * ∑ x ∈ s, f x`). Lesson: more algebra in the inductive step.
- L07 (Boss): Prove a non-trivial sum identity by finset induction requiring `induction_on`, multiple `sum_insert ha`, `card_insert_of_notMem ha`, IH, and `ring`. Must integrate L01-L06 moves.

**Dependencies**: BigOpAlgebra

**Pset partner**: PsetBigOp (W18)

---

#### W17: SummationFormulas (Example + introduces factorial)

**Type**: Example / Case-study (also introduces `Nat.factorial`)

**Promise**: By the end of this world, the learner will have proved several classical summation formulas using finset induction and big-operator algebra, and will understand `Nat.factorial` as a product.

**Object**: Concrete summation identities over `Finset.range`, including the product-to-factorial connection.

**Proof-move goals**:
- Apply finset induction to `Finset.range`
- Combine big-operator lemmas with arithmetic
- See classical formulas formalized
- Connect `∏ i in range n, (i + 1)` to `Nat.factorial n`

**Inventory changes**:
- `NewDefinition Nat.factorial`
- `NewTheorem Nat.factorial_zero Nat.factorial_succ`

**Level sketch**:
- L01: `∑ i in range (n+1), 1 = n + 1`. Warm-up induction.
- L02: `∑ i in range n, i = n * (n - 1) / 2` (or the equivalent without division). Classical sum formula.
- L03: `∏ i in range n, (i + 1) = Nat.factorial n`. Product connects to factorial.
- L04: `∑ i in range n, (2 * i + 1) = n ^ 2`. Sum of odd numbers is a perfect square.
- L05: `∑ i in range (n+1), 2^i = 2^(n+1) - 1`. Geometric sum.
- L06 (Boss): Prove a summation formula not seen in the earlier levels, requiring the full induction + big-op algebra toolkit.

**Dependencies**: FinsetInduction

**Pset partner**: PsetBigOp (W18)

---

#### W18: PsetBigOp (Problem Set)

**Type**: Pset

**Promise**: The learner retrieves big operator and finset induction skills on fresh problems.

**Level sketch**:
- L01: Unfold a sum over a concrete finset (retrieval W14).
- L02: Use sum_union and sum_const in a new context (retrieval W15).
- L03: Prove a sum identity by induction (retrieval W16).
- L04: Algebraic manipulation of a double sum (transfer W15).
- L05: Inductive proof of a product identity (transfer W16).
- L06 (Boss): Multi-step problem requiring sum decomposition, induction, and algebraic simplification. 5+ moves.

**Dependencies**: BigOpIntro, BigOpAlgebra, FinsetInduction, SummationFormulas

---

### Phase 5: Combinatorics (Worlds 19-23)

---

#### W19: BinomialCoefficients (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand `Nat.choose`, Pascal's identity, symmetry, and the factorial formula. (`Nat.factorial` was introduced in W17.)

**Theorem families**:
- `Nat.choose_zero_right`, `Nat.choose_self`, `Nat.choose_one_right`
- `Nat.choose_succ_succ` — Pascal's identity: `C(n+1, k+1) = C(n, k) + C(n, k+1)`
- `Nat.choose_symm` — `C(n, k) = C(n, n-k)`
- `Nat.choose_eq_factorial_div_factorial`

**Proof-move goals**:
- Compute `choose` for small values
- Use Pascal's identity recursively
- Apply symmetry to simplify choose expressions
- Connect choose to the factorial formula (factorial already known from W17)

**Inventory changes**:
- `NewDefinition Nat.choose`
- `NewTheorem Nat.choose_zero_right Nat.choose_self Nat.choose_succ_succ Nat.choose_symm Nat.choose_eq_factorial_div_factorial`
- `TheoremTab "Choose"`

**Level sketch**:
- L01: Factorial review and `Nat.choose` introduction — `choose 4 0 = 1`, `choose 4 4 = 1`. Lesson: boundary values. (Factorial is known from W17; this level bridges to choose.)
- L02: `Nat.choose n 1 = n`. Lesson: choosing 1 element.
- L03: Pascal's identity: `choose (n+1) (k+1) = choose n k + choose n (k+1)`. Lesson: the recursive structure.
- L04: Compute `choose 5 2 = 10` using Pascal's identity. Lesson: concrete computation.
- L05: `choose_symm`: `choose n k = choose n (n - k)`. Lesson: symmetry.
- L06: `choose n k = 0` when `k > n`. Lesson: boundary behavior. Warning: this is surprising.
- L07: Factorial formula: `choose n k = n! / (k! * (n-k)!)`. Lesson: the closed form.
- L08 (Boss): Prove a binomial coefficient identity using Pascal's identity and symmetry, requiring induction or recursive computation.

**Misconceptions addressed**: `Nat.choose n k = 0` when `k > n`.

**Dependencies**: FinsetInduction, Cardinality

**Pset partner**: PsetCombinatorics (W23)

---

#### W20: Powerset (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand `Finset.powerset` (all subsets) and `Finset.powersetCard k` (k-element subsets), and connect their cardinalities to `2^n` and `C(n,k)`.

**Theorem families**:
- `Finset.mem_powerset` — `t ∈ powerset s ↔ t ⊆ s`
- `Finset.mem_powersetCard`
- `Finset.card_powerset` — `card (powerset s) = 2 ^ card s`
- `Finset.card_powersetCard` — connects to `Nat.choose`

**Proof-move goals**:
- Prove membership in powerset/powersetCard
- Prove cardinality of powerset = 2^n
- Connect powersetCard to Nat.choose
- See the set-theoretic meaning of binomial coefficients

**Inventory changes**:
- `NewDefinition Finset.powerset Finset.powersetCard`
- `NewTheorem Finset.mem_powerset Finset.mem_powersetCard Finset.card_powerset Finset.card_powersetCard`

**Level sketch**:
- L01: `Finset.powerset` — enumerate all subsets of `{1, 2}`. Lesson: what powerset produces.
- L02: `mem_powerset` — `t ∈ powerset s ↔ t ⊆ s`. Lesson: membership characterization.
- L03: `card_powerset` — `card (powerset s) = 2 ^ card s`. Lesson: 2^n subsets.
- L04: `Finset.powersetCard k s` — the k-element subsets. Lesson: restricted powerset.
- L05: `card_powersetCard` — connects to `Nat.choose`. Lesson: C(n,k) counts k-element subsets.
- L06: Enumerate `powersetCard 2 {1,2,3}` — see the 3 two-element subsets concretely. Lesson: concretization.
- L07 (Boss): Prove a result connecting powerset cardinality to binomial coefficients, requiring both set-theoretic and combinatorial reasoning.

**Dependencies**: BinomialCoefficients

**Pset partner**: PsetCombinatorics (W23)

---

#### W21: BinomialTheorem (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will understand and apply the binomial theorem (`add_pow`) and the row-sum identity (`sum_range_choose`).

**Theorem families**:
- `add_pow` — `(x + y)^n = ∑ k in range (n+1), choose n k * x^k * y^(n-k)`
- `Nat.sum_range_choose` — `∑ k in range (n+1), choose n k = 2^n`
- Connection between `add_pow` and `card_powerset`

**Proof-move goals**:
- Apply the binomial theorem to expand `(x+y)^n`
- Specialize the binomial theorem to get counting identities
- Prove `sum_range_choose` (possibly by specializing `add_pow` to x=y=1)
- Use big-operator machinery in a combinatorial context

**Inventory changes**:
- `NewTheorem add_pow Nat.sum_range_choose`

**Level sketch**:
- L01: State the binomial theorem: `add_pow`. Lesson: what the theorem says.
- L02: Specialize to `n = 2`: `(x+y)^2 = x^2 + 2*x*y + y^2`. Lesson: concrete case.
- L03: Specialize to `n = 3`. Lesson: practice with larger expansion.
- L04: Specialize to `x = 1, y = 1`: derive `sum_range_choose`. Lesson: row sum = 2^n.
- L05: Specialize to `x = 1, y = -1`: derive alternating sum identity. Lesson: signs alternate.
- L06: Connection: why `card (powerset s) = 2^n` follows from counting subsets of each size. Lesson: double counting preview.
- L07 (Boss): Prove a binomial identity by applying `add_pow` with specific values and simplifying using big-operator algebra.

**Dependencies**: Powerset, BigOpAlgebra

**Pset partner**: PsetCombinatorics (W23)

---

#### W22: PascalsTriangle (Example)

**Type**: Example / Case-study

**Promise**: By the end of this world, the learner will have explored concrete properties of Pascal's triangle and used them to verify counting identities.

**Object**: Pascal's triangle as organized by `Nat.choose` and `Finset.Nat.antidiagonal`.

**Proof-move goals**:
- Compute specific entries of Pascal's triangle
- Verify identities on concrete values before proving them abstractly
- Use `Finset.Nat.antidiagonal` to express pairs summing to `n`

**Inventory changes**:
- `NewDefinition Finset.Nat.antidiagonal`
- `NewTheorem Finset.Nat.mem_antidiagonal`

**Level sketch**:
- L01: Compute row 5 of Pascal's triangle. Lesson: concrete computation.
- L02: Verify `∑ k in range 6, choose 5 k = 32` concretely. Lesson: row sum.
- L03: `Finset.Nat.antidiagonal n` — the pairs `(a, b)` with `a + b = n`. Lesson: new construction.
- L04: Rewrite a sum over `range (n+1)` as a sum over `antidiagonal n`. Lesson: reindexing.
- L05: Verify a specific case of `choose n k * choose k j = choose n j * choose (n-j) (k-j)`. Lesson: compound identity.
- L06 (Boss): Prove a result about Pascal's triangle entries using multiple identities.

**Dependencies**: BinomialTheorem

**Pset partner**: PsetCombinatorics (W23)

---

#### W23: PsetCombinatorics (Problem Set)

**Type**: Pset

**Promise**: The learner retrieves combinatorics skills on fresh problems.

**Level sketch**:
- L01: Binomial coefficient computation not seen before (retrieval W19).
- L02: Powerset membership or cardinality (retrieval W20).
- L03: Application of binomial theorem (retrieval W21).
- L04: Sum over antidiagonal (retrieval W22).
- L05: Proof combining Pascal's identity with powerset counting (integration).
- L06 (Boss): Multi-step combinatorics problem requiring factorial, choose, powerset, and big-operator moves. 5+ integrated moves.

**Dependencies**: BinomialCoefficients, Powerset, BinomialTheorem, PascalsTriangle

---

### Phase 6: Advanced Topics (Worlds 24-26)

---

#### W24: Products (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to work with `Finset.product`, `Finset.sigma`, `Finset.diag`, and `Finset.offDiag`, and prove cardinality and membership results about product constructions.

**Theorem families**:
- `Finset.mem_product`, `Finset.card_product`
- `Finset.mem_sigma`, `Finset.card_sigma`
- `Finset.mem_diag`, `Finset.mem_offDiag`
- `Finset.product` notation: `s ×ˢ t`

**Proof-move goals**:
- Prove membership in `s ×ˢ t`
- Compute `card (s ×ˢ t)` = `card s * card t` (already seen in W09, now with the product construction)
- Work with dependent products (`sigma`)
- Identify diagonal and off-diagonal pairs

**Inventory changes**:
- `NewDefinition Finset.product Finset.sigma Finset.diag Finset.offDiag`
- `NewTheorem Finset.mem_product Finset.mem_sigma Finset.mem_diag Finset.mem_offDiag Finset.card_sigma`

**Level sketch**:
- L01: `s ×ˢ t` — the cartesian product. Enumerate `{1,2} ×ˢ {3,4}`. Lesson: product construction.
- L02: `mem_product` — membership characterization. Lesson: `(a, b) ∈ s ×ˢ t ↔ a ∈ s ∧ b ∈ t`.
- L03: `card_product` revisited — now using the `Finset.product` construction. Lesson: product rule.
- L04: `Finset.sigma` — dependent product. Lesson: when the second component depends on the first.
- L05: `Finset.diag s` — diagonal pairs `{(a, a) | a ∈ s}`. Lesson: diagonal.
- L06: `Finset.offDiag s` — off-diagonal pairs. Lesson: complement of diagonal.
- L07 (Boss): Prove a cardinality or membership result about a product/sigma/diag construction.

**Dependencies**: Cardinality

---

#### W25: Finsupp (Lecture/Example)

**Type**: Lecture (light) + Example

**Promise**: By the end of this world, the learner will understand `Finsupp` as a finitely supported function, construct `Finsupp` values using `single`, and reason about their support.

**Theorem families**:
- `Finsupp.support`, `Finsupp.single`, `Finsupp.mapDomain`
- `Finsupp.single_apply`, `Finsupp.support_single_ne_zero`

**Proof-move goals**:
- Construct a `Finsupp` using `single` and understand its support
- Evaluate `Finsupp.single_apply` (the if-then-else behavior)
- Understand `Finsupp.support` as a `Finset`

**Inventory changes**:
- `NewDefinition Finsupp Finsupp.support Finsupp.single`
- `NewTheorem Finsupp.single_apply Finsupp.support_single_ne_zero`
- `TheoremTab "Finsupp"`

**Level sketch**:
- L01: `Finsupp.single 3 7 : ℕ →₀ ℤ` — a function that is 7 at 3 and 0 elsewhere. Lesson: what Finsupp is.
- L02: `Finsupp.support` — the set where the function is nonzero. Lesson: finiteness of support.
- L03: `Finsupp.single_apply` — evaluating a single. Lesson: if-then-else behavior.
- L04: Adding two `Finsupp` values — support of sum ⊆ union of supports. Lesson: support algebra.
- L05 (Boss): Construct a Finsupp, reason about its support, and prove an evaluation identity. Integration of L01-L04 moves.

**Dependencies**: Fintype

---

#### W26: Matrices (Lecture/Example)

**Type**: Lecture (light) + Example

**Promise**: By the end of this world, the learner will understand `Matrix` as a function `m -> n -> α`, and will be able to construct, decompose, and prove equality of matrices using function reasoning.

**Theorem families**:
- `Matrix` is `m -> n -> α`
- `Matrix.diagonal`, `Matrix.diag`, `Matrix.transpose`
- `Matrix.ext_iff`

**Proof-move goals**:
- See that `Matrix (Fin 2) (Fin 2) ℤ` is just a function
- Prove properties of concrete matrices using function reasoning
- Apply matrix extensionality

**Inventory changes**:
- `NewDefinition Matrix Matrix.diagonal Matrix.transpose`
- `NewTheorem Matrix.ext_iff`
- `TheoremTab "Matrix"`

**Level sketch**:
- L01: `Matrix (Fin 2) (Fin 2) ℤ` is just `Fin 2 -> Fin 2 -> ℤ`. Lesson: matrices are functions. Demystification.
- L02: `Matrix.diagonal` — a diagonal matrix. Lesson: constructing structured matrices.
- L03: `Matrix.transpose` — transposing a matrix. Lesson: `transpose M i j = M j i`.
- L04: `Matrix.ext_iff` — two matrices are equal iff they agree at every entry. Lesson: function extensionality for matrices.
- L05 (Boss): Prove a property of a concrete 2x2 matrix using function reasoning and matrix extensionality.

**Dependencies**: Fintype, FinTuples

---

### Phase 7: Capstone (Worlds 27-29)

---

#### W27: CountingTechniques (Lecture)

**Type**: Lecture

**Promise**: By the end of this world, the learner will be able to apply double counting, bijective proofs, and the pigeonhole principle — the three major combinatorial proof techniques.

**Theorem families**:
- `Fintype.card_congr` — bijective counting via `Equiv` (revisited from W11, now as a technique)
- `Finset.card_le_card_of_injOn` / `Fintype.card_le_of_injective` — injection-based bounds
- `Finset.card_lt_card` — strict subset means strictly fewer
- Pigeonhole: `Fintype.exists_ne_map_eq_of_card_lt` (or equivalent)
- Double counting: `∑ x ∈ s, f x` computed two ways

**Proof-move goals**:
- Prove two sets have equal cardinality by constructing a bijection
- Prove cardinality bounds using injections and surjections
- Apply the pigeonhole principle
- Compute the same quantity two ways (double counting)
- Combine counting techniques with big-operator algebra

**Inventory changes**:
- `NewTheorem Finset.card_lt_card Fintype.card_le_of_injective`
- Any pigeonhole-specific theorems

**Level sketch**:
- L01: Bijective counting revisited — build an `Equiv` between two types and conclude equal card. Lesson: bijective proof as technique.
- L02: Injection-based bound — if `f : s -> t` is injective, then `card s ≤ card t`. Lesson: injection gives upper bound.
- L03: Strict subset means strictly fewer elements. Lesson: `card_lt_card`.
- L04: Pigeonhole principle — if `card α > card β` then no injection `α -> β` exists. Lesson: too many pigeons.
- L05: Application of pigeonhole to a concrete problem. Lesson: applying the principle.
- L06: Double counting — compute `∑ x ∈ s, f x` in two different ways. Lesson: same quantity, two decompositions.
- L07: Application of double counting to a combinatorial identity. Lesson: the technique in action.
- L08 (Boss): A substantial proof requiring at least two of: bijective argument, pigeonhole, double counting, big-operator algebra, and cardinality arithmetic. Full integration.

**Dependencies**: PsetCardinality, PsetBigOp, PsetCombinatorics (should come after all main content)

---

#### W28: PsetCounting (Problem Set)

**Type**: Pset

**Promise**: The learner retrieves and transfers bijective proof, pigeonhole, and double counting skills on fresh problems without scaffolding.

**Proof-move goals**:
- Unsupported retrieval of bijective counting, pigeonhole, and double counting from W27
- Transfer to fresh surface forms not seen in W27
- Integration of counting techniques with big-operator and cardinality machinery from earlier phases

**Inventory changes**: None new. All W27 inventory available.

**Level sketch**:
- L01: Bijective proof on a fresh pair of types — construct an Equiv and conclude equal cardinality (retrieval of W27 L01).
- L02: Pigeonhole application in a new context — e.g., among `n+1` integers, two share the same remainder mod `n` (transfer of W27 L04-L05).
- L03: Double counting on a fresh combinatorial identity — compute the same sum two ways (retrieval of W27 L06-L07).
- L04: Injection-based cardinality bound in a new setting (transfer of W27 L02).
- L05: Integration problem requiring pigeonhole + big-operator algebra or cardinality arithmetic.
- L06 (Boss): Multi-step counting proof requiring at least two of bijection, pigeonhole, double counting, combined with earlier skills. 5+ integrated moves from W27 and prior phases.

**Dependencies**: CountingTechniques

---

#### W29: Finale (Review/Capstone)

**Type**: Review + Capstone

**Promise**: The learner integrates all major skills from the course in a series of challenging problems that combine Fin, Finset, Fintype, big operators, and combinatorics.

**Proof-move goals**:
- Full integration across all 7 phases
- Multi-step proofs requiring planning
- Transfer to genuinely new surface forms

**Level sketch**:
- L01: A Fintype cardinality problem using products and bijection (integration of Phases 1, 3).
- L02: A big-operator identity proved by finset induction (integration of Phase 4).
- L03: A combinatorial identity using powerset and binomial coefficients (integration of Phase 5).
- L04: A double-counting proof connecting two different summations (integration of Phases 4, 5, 7).
- L05: A problem involving Finset.image, cardinality, and pigeonhole (integration of Phases 2, 3, 7).
- L06 (Boss): The course's hardest problem. A multi-step proof requiring Fin navigation, Finset operations, big-operator manipulation, finset induction, and a counting technique. 7+ integrated moves. Multiple valid proof paths.

**Dependencies**: CountingTechniques, PsetCounting, Products, Finsupp, Matrices

---

## 5. Coverage Closure Table

For each core item, the five coverage stages mapped to specific worlds.

| Core Item | Introduce | Supported Practice | Unsupported Retrieval | Integration | Transfer |
|-----------|-----------|-------------------|----------------------|-------------|----------|
| `Fin n` (what it is, elements, val) | W01 | W02, W03 | W04 | W12, W25 | W29 |
| `Fin` navigation (succ, castSucc, last) | W02 | W03, W04 | W04 | W12 | W29 |
| Tuples (`Fin n -> α`, cons, snoc) | W03 | W04 | W12 | W26 | W29 |
| `Finset` membership | W05 | W06, W07 | W08 | W09 | W13, W29 |
| `Finset.Nonempty` → witness | W05 | W09 | W13 | W27 | W29 |
| `Finset` operations (∪, ∩, \, filter) | W06 | W07, W08 | W08 | W09 | W13, W29 |
| `simp only [...]` with Finset lemmas | W06 | W08 | W13 | W15 | W29 |
| `Finset.ext` (set equality by ext) | W06 | W07 | W08 | W09, W15 | W13 |
| `Finset.image` and injectivity | W07 | W08 | W09, W13 | W27 | W29 |
| `Finset.card` and card_* lemmas | W09 | W11, W12 | W13 | W20, W24 | W23, W29 |
| Inclusion-exclusion | W09 | W12 | W13 | W27 | W29 |
| List -> Multiset -> Finset ladder | W10 | W10, W14 (L08 Multiset connection) | W13 | W14 (sum is Multiset-based) | W29 |
| `Fintype`, `univ`, `Fintype.card` | W11 | W12 | W13 | W24, W25 | W27, W29 |
| Fintype composition (card_prod, card_sum, card_fun) | W11 | W12 | W13 | W24 | W29 |
| `Equiv`-based bijective counting | W11 | W12 | W13 | W27 | W29 |
| `calc` blocks | W15 | W17 | W18 | W21 | W29 |
| `ring` / `ring_nf` | W15 | W17 | W18 | W21 | W29 |
| Big operators (`∑`, `∏`) basics | W14 | W15 | W18 | W16, W17 | W21, W29 |
| Big operator algebra (union, filter, const, distrib) | W15 | W17 | W18 | W16, W21 | W23, W29 |
| Rewriting under binders (`sum_congr`) | W14 | W15 | W18 | W21 | W29 |
| Finset induction | W16 | W17 | W18 | W19, W21 | W23, W29 |
| `Nat.factorial` | W17 | W19, W22 | W23 | W19 (choose formula) | W29 |
| `Nat.choose` and Pascal's identity | W19 | W20, W22 | W23 | W21 | W29 |
| `choose_symm` | W19 | W22 | W23 | W21 | W29 |
| `Finset.powerset`, `powersetCard` | W20 | W22 | W23 | W21 | W29 |
| `card_powerset` = 2^n | W20 | W22 | W23 | W21 | W29 |
| `card_powersetCard` connects to choose | W20 | W22 | W23 | W21 | W29 |
| Binomial theorem (`add_pow`) | W21 | W22 | W23 | W27 | W29 |
| `sum_range_choose` = 2^n | W21 | W22 | W23 | W27 | W29 |
| Double counting | W27 | W27, W28 | W28 | W29 | W29 |
| Pigeonhole | W27 | W27, W28 | W28 | W29 | W29 |
| `Finset.product` (s ×ˢ t) | W24 | W24 | W29 | W29 | W29 |
| `Finsupp` | W25 | W25 | W29 | W29 | — |
| `Matrix` as function | W26 | W26 | W29 | W29 | — |

## 6. Inventory Release Plan

### Phase 1: Finite Types (W01-W04)

| World | New Tactics | New Theorems/Definitions | Disabled | Rationale |
|-------|-----------|--------------------------|----------|-----------|
| W01 | `omega` | `Fin`, `Fin.val`, `Fin.mk`, `Fin.ext_iff` | `fin_cases`, `interval_cases`, `decide`, `norm_num` | `omega` needed for Fin arithmetic; `fin_cases` disabled to force manual case analysis |
| W02 | — | `Fin.succ`, `Fin.castSucc`, `Fin.last`, value lemmas | `fin_cases` | Still forcing manual case analysis |
| W03 | `funext` | `Fin.cons`, `Fin.snoc`, `Fin.tail`, cons/snoc lemmas | `fin_cases` | `funext` is a new tactic for function extensionality |
| W04 (pset) | — | (all W01-W03 available) | `fin_cases` | Retrieval with same inventory |

### Phase 2: Finite Sets (W05-W08)

| World | New Tactics | New Theorems/Definitions | Disabled | Rationale |
|-------|-----------|--------------------------|----------|-----------|
| W05 | `decide` (re-enabled) | `Finset`, `∅`, `singleton`, `insert`, `range`, mem_* lemmas, `Finset.Nonempty` | `ext`, lattice aliases, `norm_num` | `decide` useful for small finset goals; `ext` delayed to W06; `Nonempty` → witness move introduced |
| W06 | `ext`, `simp_only` | union/inter/sdiff/filter, mem_* lemmas, `ext_iff`, `subset_iff` | lattice aliases (sup_comm, inf_comm, etc.) | `ext` and `simp only` are new tactics; lattice aliases always disabled for Finset work |
| W07 | — | `Finset.image`, `card_image_le`, `card_image_of_injective` | lattice aliases | No new tactics; focus on image + cardinality interaction. `Finset.map` deferred to a later world. |
| W08 (pset) | — | (all W05-W07 available) | lattice aliases | Retrieval |

### Phase 3: Cardinality and Structure (W09-W13)

| World | New Tactics | New Theorems/Definitions | Disabled | Rationale |
|-------|-----------|--------------------------|----------|-----------|
| W09 | — | `Finset.card`, all card_* lemmas, `card_union_add_card_inter`, `card_product` | lattice aliases, `norm_num` | `norm_num` stays disabled — `omega` suffices for all cardinality arithmetic |
| W10 | — | `List`, `Multiset`, `List.Perm`, `List.Nodup`, conversion lemmas | lattice aliases | No new tactics; focus on understanding the types |
| W11 | — | `Fintype`, `Finset.univ`, `Fintype.card`, card_fin/prod/sum/fun, `card_congr` | lattice aliases | No new tactics; focus on the typeclass and its instances |
| W12 (example) | — | `Nat.descFactorial`, `Nat.descFactorial_zero`, `Nat.descFactorial_succ` + all W09-W11 | lattice aliases | Introduces descFactorial for counting injections; retrieval and concretization |
| W13 (pset) | — | (all W09-W12 available) | lattice aliases | Retrieval |

### Phase 4: Big Operators (W14-W18)

| World | New Tactics | New Theorems/Definitions | Disabled | Rationale |
|-------|-----------|--------------------------|----------|-----------|
| W14 | — | `Finset.sum`, `Finset.prod`, sum_empty/singleton/insert, sum_congr, prod analogues | `norm_num` (early levels only), lattice aliases | Disable `norm_num` on early levels to force manual unfolding |
| W15 | `calc`, `ring`, `ring_nf` | sum_union, sum_filter, sum_const, sum_add_distrib, prod_mul_distrib, sum_comm | lattice aliases | `calc` blocks for chained equalities; `ring`/`ring_nf` for algebraic simplification; focus on algebraic moves |
| W16 | — (induction in new context) | `Finset.induction_on` | lattice aliases | `induction` tactic in new context (finsets) |
| W17 (example) | — | `Nat.factorial`, `Nat.factorial_zero`, `Nat.factorial_succ` + all W14-W16 | lattice aliases | Introduces factorial; retrieval + concrete formulas |
| W18 (pset) | — | (all W14-W17 available) | lattice aliases | Retrieval |

### Phase 5: Combinatorics (W19-W23)

| World | New Tactics | New Theorems/Definitions | Disabled | Rationale |
|-------|-----------|--------------------------|----------|-----------|
| W19 | — | `Nat.choose`, choose_succ_succ, choose_symm, factorial formula (factorial already from W17) | lattice aliases | Focus on choose and key identities; factorial known |
| W20 | — | `Finset.powerset`, `Finset.powersetCard`, card_powerset, card_powersetCard | lattice aliases | Connect subsets to counting |
| W21 | — | `add_pow`, `Nat.sum_range_choose` | lattice aliases | The binomial theorem |
| W22 (example) | — | `Finset.Nat.antidiagonal`, `mem_antidiagonal` | lattice aliases | Pascal's triangle exploration |
| W23 (pset) | — | (all W19-W22 available) | lattice aliases | Retrieval |

### Phase 6: Advanced Topics (W24-W26)

| World | New Tactics | New Theorems/Definitions | Disabled | Rationale |
|-------|-----------|--------------------------|----------|-----------|
| W24 | — | `Finset.product`, `Finset.sigma`, `Finset.diag`, `Finset.offDiag` | lattice aliases | Product constructions |
| W25 | — | `Finsupp`, `Finsupp.single`, `Finsupp.support` | lattice aliases | Finitely supported functions |
| W26 | — | `Matrix`, `Matrix.diagonal`, `Matrix.transpose`, `Matrix.ext_iff` | lattice aliases | Matrices as functions |

### Phase 7: Capstone (W27-W29)

| World | New Tactics | New Theorems/Definitions | Disabled | Rationale |
|-------|-----------|--------------------------|----------|-----------|
| W27 | — | `Finset.card_lt_card`, `Fintype.card_le_of_injective`, pigeonhole lemma | lattice aliases | Counting techniques |
| W28 (pset) | — | (all W27 available) | lattice aliases | Retrieval of counting techniques |
| W29 | — | (full inventory available) | lattice aliases only | Capstone — everything available |

### Global Disabled (all worlds, baseline)
- `trivial`, `decide` (re-enabled W05+), `native_decide`, `simp`, `aesop`, `simp_all`
- `tauto` (when propositional logic is the point)
- Lattice aliases: `sup_comm`, `inf_comm`, `inf_le_left`, `sup_le`, `le_antisymm`, `sup_eq_left`, `inf_eq_left`, etc. — always disabled alongside Finset ∪/∩

### Per-level gating notes
- `norm_num`: disabled throughout W01-W09. In W09 (Cardinality), `omega` suffices for all arithmetic. Consider re-enabling in W14 (Big Operators) for concrete sum computations.
- `fin_cases`: disabled W01-W04 (force manual Fin case analysis); consider enabling late
- `ext`: disabled before W06 L07 to force discovery of why extensionality is needed; enabled from W06 L07 onward
- `by_cases`: gate when the learner should find the case split themselves
- Lattice exploit lemmas: always disabled when working with Finset operations

## 7. Boss Map

| World | Boss Description | Prerequisite Skills (level → skill) |
|-------|-----------------|--------------------------------------|
| W01 | Fin element construction + val + ext | L01→construct, L02→val, L03→ext, L04-L06→boundary |
| W02 | Navigate Fin(n+1) using last, castSucc, case analysis | L01→last, L02→castSucc, L03→succ, L05-L06→cases |
| W03 | Build+decompose tuple, prove equality by funext | L02→cons, L04→snoc, L05→tail, L06→funext |
| W04 | Multi-step Fin problem, 5+ moves | W01-W03 all skills |
| W05 | Membership in compound finset expression | L01-L02→mem_insert, L03→mem_singleton, L05→mem_range, L06→literal, L08→Nonempty |
| W06 | Set identity via ext + mem_union/inter + simp only + logic | L01-L04→mem_ops, L05→subset, L07→ext, L08→lattice warning, L09→simp only |
| W07 | Image cardinality requiring witness + injectivity | L02→mem_image, L04→non-injective, L05→injective |
| W08 | Multi-step finset problem, 5+ moves | W05-W07 all skills |
| W09 | Cardinality of compound expression using card_*, incl-excl, arithmetic | L03→card_insert, L06→incl-excl, L08→card_product |
| W10 | List/Multiset/Finset conversion requiring Nodup + Perm | L03→Perm, L06→Nodup, L07→conversion |
| W11 | Card of composite type using card_prod/sum/fun | L04→card_prod, L05→card_sum, L06→card_fun, L07→ℕ not Fintype, L08→card_congr |
| W12 | Card of non-trivial type using card_* + Equiv + incl-excl practice | W11 card lemmas + Equiv construction + L06→inclusion-exclusion |
| W13 | Integration of cardinality, Fintype, ext, 5+ moves | W09-W12 all skills |
| W14 | Sum computation using sum_insert + sum_congr + simplification | L03→sum_singleton, L04→sum_insert, L07→sum_congr, L08→Multiset connection |
| W15 | Algebraic identity requiring decomposition + distributivity + calc + ring | L01→sum_union, L03→sum_const, L04→sum_add_distrib, L08→calc, L09→ring |
| W16 | Sum identity by induction: base + step with sum_insert + IH + algebra | L01-L03→induction setup, L04-L05→full proofs |
| W17 | Classical summation formula by induction + introduces factorial | W16 induction + W14-W15 algebra, L03→factorial connection |
| W18 | Multi-step big-op problem, 5+ moves | W14-W17 all skills |
| W19 | Binomial identity using Pascal + symmetry + induction | L03→Pascal, L05→symmetry, L07→factorial formula |
| W20 | Powerset cardinality connecting to choose | L03→card_powerset, L05→card_powersetCard |
| W21 | Binomial theorem specialization + simplification | L01→add_pow, L04→row sum |
| W22 | Pascal's triangle result using multiple identities | W19-W21 identities |
| W23 | Multi-step combinatorics, 5+ moves | W19-W22 all skills |
| W24 | Product/sigma/diag cardinality or membership | L02→mem_product, L04→sigma, L05-L06→diag |
| W25 | Finsupp construction + support reasoning | L01→single, L02→support, L03→single_apply, L04→support algebra |
| W26 | Concrete matrix property via function reasoning | L01→matrix is function, L04→matrix ext |
| W27 | Major proof using 2+ of: bijection, pigeonhole, double counting | L01→bijection, L04→pigeonhole, L06→double counting |
| W28 | Counting technique retrieval, 5+ moves | W27 all skills on fresh problems |
| W29 | Course capstone, 7+ moves, multiple valid paths | All phases |

## 8. Transfer and Retrieval Plan

### High-value move: Prove `x ∈ s` by construction
- **First appears**: W05 (FinsetBasics) — prove membership in literal finsets
- **Supported practice**: W06 (FinsetOperations) — membership in ∪, ∩, filter
- **Less support**: W08 (PsetFinset) — fresh problems, no scaffolding
- **Fresh surface**: W09 (Cardinality) — membership needed as hypothesis for card lemmas
- **Paper transfer**: "To show x is in the set, exhibit the element and check the membership condition"

### High-value move: Prove `s = t` by extensionality
- **First appears**: W06 (FinsetOperations) — introduce `ext` tactic
- **Supported practice**: W07 (FinsetImage), W08 (PsetFinset)
- **Less support**: W13 (PsetCardinality) — ext needed without prompting
- **Fresh surface**: W26 (Matrices) — matrix extensionality
- **Paper transfer**: "Two sets are equal iff they have the same elements"

### High-value move: Cardinality arithmetic via card_* lemmas
- **First appears**: W09 (Cardinality)
- **Supported practice**: W12 (CountingTypes), W13 (PsetCardinality)
- **Less support**: W20 (Powerset) — card_powerset without card being the lesson
- **Fresh surface**: W24 (Products) — card_sigma, card_offDiag
- **Paper transfer**: "Count elements by decomposing the set and adding/multiplying"

### High-value move: Finset induction
- **First appears**: W16 (FinsetInduction)
- **Supported practice**: W17 (SummationFormulas)
- **Less support**: W18 (PsetBigOp)
- **Fresh surface**: W19 (BinomialCoefficients) — induction on choose
- **Paper transfer**: "Prove by induction on the size of the set; base case is empty, inductive step adds one element"

### High-value move: Big-operator manipulation (sum_insert, sum_congr, etc.)
- **First appears**: W14 (BigOpIntro)
- **Supported practice**: W15 (BigOpAlgebra), W17 (SummationFormulas)
- **Less support**: W18 (PsetBigOp)
- **Fresh surface**: W21 (BinomialTheorem) — sums in combinatorial context
- **Paper transfer**: "Rewrite sums by splitting, filtering, or rewriting the summand"

### High-value move: Bijective counting via Equiv
- **First appears**: W11 (Fintype) — `Fintype.card_congr`
- **Supported practice**: W12 (CountingTypes)
- **Less support**: W13 (PsetCardinality)
- **Fresh surface**: W27 (CountingTechniques) — as a named technique
- **Paper transfer**: "Two sets have the same size if you can pair their elements one-to-one"

### High-value move: Binomial coefficient identities
- **First appears**: W19 (BinomialCoefficients)
- **Supported practice**: W20 (Powerset), W22 (PascalsTriangle)
- **Less support**: W23 (PsetCombinatorics)
- **Fresh surface**: W21 (BinomialTheorem) — choose inside sums
- **Paper transfer**: "Use Pascal's identity, symmetry, or the factorial formula as needed"

### High-value move: Double counting
- **First appears**: W27 (CountingTechniques)
- **Supported practice**: W27 (later levels), W28 (PsetCounting)
- **Less support**: W28 (PsetCounting boss)
- **Fresh surface**: W29 (Finale) — new context
- **Paper transfer**: "Compute the same quantity in two different ways, then equate"

## 9. Misconception Plan

| Misconception | Where Addressed | How |
|--------------|----------------|-----|
| `Fin n` elements start at 0, not 1 | W01 L04 | Explicit warning in level intro; exercise requiring 0-based indexing |
| `↑i` (coercion) vs `i.val` — same thing | W01 L02 | Show both notations; explain they are interchangeable |
| `Fin 0` is empty (no elements) | W01 L04 | Explicit level constructing a proof about `Fin 0` |
| `Finset.range n` is `{0,...,n-1}` not `{0,...,n}` | W05 L05 | Explicit warning; exercise: `n ∉ range n` |
| `{a, b, c}` is sugar for nested `insert` | W05 L06 | Show the unfolding explicitly |
| `insert a s = s` when `a ∈ s` (idempotence) | W05 L07 | Explicit level with counterexample |
| `∪`/`∩` are lattice `⊔`/`⊓` underneath | W06 L08 | Warning level; show goal state with lattice notation |
| `Finset.image` can shrink cardinality | W07 L04 | Explicit counterexample: `image (fun _ => 0) {1,2,3}` |
| `Multiset ≠ Finset` (duplicates matter) | W10 L05, L08 | Concrete comparison: same elements, different cards |
| `List ≠ Multiset` (order matters) | W10 L02, L04 | Concrete comparison: `[1,2,3] ≠ [3,1,2]` as lists, equal as multisets |
| `ℕ` has no `Fintype` instance — not every type is finite | W11 L07 | Explicit level showing that `Fintype.card ℕ` is a type error; warning in world intro |
| Big operator over empty set = identity (0 or 1) | W14 L02, L06 | Explicit levels for sum_empty = 0 and prod_empty = 1 |
| `Nat.choose n k = 0` when `k > n` | W19 L06 | Explicit level with warning |
| `0! = 1` (convention, not obvious) | W17 L03 | Called out in level intro (factorial introduced in W17) |
| `Finset.sum` requires `AddCommMonoid` | W14 L01 | Mentioned in docs, not a full level |
| `Matrix m n α` is just a function | W26 L01 | Central lesson — demystification |

## 10. Major Risks

### Risk 1: Coercion confusion in early Fin worlds
`Fin n` elements have a natural number value accessible via `↑i` or `i.val`, but the coercion can create confusing goal states (e.g., `↑i < n` vs `i.val < n`). This is pervasive and hard to diagnose from error messages.

**Mitigation**: Dedicate explicit levels in W01 to the coercion story. Show what `↑` does, when it appears, and that it equals `.val`. Use `omega` to close arithmetic goals cleanly. Provide clear doc entries.

### Risk 2: Lattice alias exploits for Finset operations
Finset `∪`/`∩` are lattice `⊔`/`⊓`. Every Finset identity has a lattice-level alias (`sup_comm`, `inf_le_left`, etc.) that must be disabled alongside the Finset-specific lemma. Missing even one alias creates an exploit path.

**Mitigation**: Maintain a comprehensive disable list for lattice aliases. Test each level for exploit paths. Disable `sup_comm`, `inf_comm`, `inf_le_left`, `sup_le`, `le_antisymm`, `sup_eq_left`, `inf_eq_left`, `bot_le`, `le_top`, and any others discovered during authoring.

### Risk 3: `norm_num` and `decide` one-shotting levels
Both `norm_num` and `decide` can close many finite-object goals automatically, bypassing the intended proof structure.

**Mitigation**: Disable `decide` until W05, `norm_num` until W09. Gate per-level thereafter when manual reasoning is the lesson. The baseline disables `simp` and `aesop`.

### Risk 4: Big-operator notation overwhelming
The `∑ x ∈ s, f x` notation involves binders, which interact with tactics in unfamiliar ways (e.g., `simp` vs `rw` under binders). Combined with the new algebraic proof moves, this is novelty hotspot #2.

**Mitigation**: Start with sums over tiny literal finsets where the sum unfolds to 2-3 terms. Introduce notation before proof moves. Dedicate separate levels to `sum_congr` (rewriting under binders) vs `sum_insert` (structural manipulation).

### Risk 5: Finset induction hypothesis shape
Finset induction introduces a hypothesis `a ∉ s` that has no analogue in ℕ induction. Learners may not know what to do with it.

**Mitigation**: Precede induction with a level that shows the `insert` constructor explicitly. Let the learner see the `insert a s` structure before doing induction. Provide clear hints about using `sum_insert` (which requires the `a ∉ s` hypothesis).

### Risk 6: Course length
29 worlds is substantial. Learner fatigue or dropout is a risk, especially in the middle phases.

**Mitigation**: Each phase ends with a pset that provides closure. Example worlds provide variety and concreteness. The course can be paused after any pset world and resumed later. World independence (within limits) allows skipping ahead.

### Risk 7: Double counting and pigeonhole coverage
These core counting techniques are introduced in W27 (CountingTechniques). W28 (PsetCounting) provides dedicated unsupported retrieval and transfer practice before the Finale.

**Mitigation**: Seeds are planted earlier — injection-based cardinality in W07/W09, bijective counting in W11/W12. W27 names and consolidates techniques already partially used. W28 provides dedicated practice. W29 (Finale) provides final integration.

### Risk 8: Finsupp and Matrix depth
These are supporting topics split into separate worlds (W25 Finsupp, W26 Matrices) to maintain single center-of-gravity per world.

**Mitigation**: Each world is light (5 levels). If either proves too thin during authoring, merge relevant levels into W24 (Products) and drop the world. If too thick, expand. Authoring will determine the right depth.

## 11. World Dependency DAG

The explicit dependency graph. An arrow `A → B` means "B requires A."

```
Phase 1 (Fin):
  W01 (MeetFin)
   └→ W02 (FinNavigation)
       └→ W03 (FinTuples)
           └→ W04 (PsetFin) ←── W01, W02

Phase 2 (Finset):
  W03 → W05 (FinsetBasics)
         └→ W06 (FinsetOperations)
             └→ W07 (FinsetImage)
                 └→ W08 (PsetFinset) ←── W05, W06

Phase 3 (Cardinality):
  W07 → W09 (Cardinality)
         └→ W10 (AbstractionLadder)
             └→ W11 (Fintype)
                 └→ W12 (CountingTypes)
                     └→ W13 (PsetCardinality) ←── W09, W10, W11

Phase 4 (Big Operators):
  W06 → W14 (BigOpIntro)
         └→ W15 (BigOpAlgebra)
             └→ W16 (FinsetInduction)
                 └→ W17 (SummationFormulas)
                     └→ W18 (PsetBigOp) ←── W14, W15, W16

Phase 5 (Combinatorics):
  W16, W09 → W19 (BinomialCoefficients)
              └→ W20 (Powerset)
  W20, W15 → W21 (BinomialTheorem)
              └→ W22 (PascalsTriangle)
                  └→ W23 (PsetCombinatorics) ←── W19, W20, W21

Phase 6 (Advanced):
  W09 → W24 (Products)
  W11 → W25 (Finsupp)
  W11, W03 → W26 (Matrices)

Phase 7 (Capstone):
  W13, W18, W23 → W27 (CountingTechniques)
                   └→ W28 (PsetCounting)
  W27, W28, W24, W25, W26 → W29 (Finale)
```

### Cross-phase dependencies (non-obvious edges)

| From | To | Reason |
|------|----|--------|
| W03 (FinTuples) | W05 (FinsetBasics) | Learner needs subtype/Fin fluency |
| W06 (FinsetOperations) | W14 (BigOpIntro) | Needs membership, insert for sum_insert |
| W07 (FinsetImage) | W09 (Cardinality) | card_image_le from W07 |
| W09 (Cardinality) | W19 (BinomialCoefficients) | Cardinality arithmetic needed |
| W09 (Cardinality) | W24 (Products) | card_product revisited |
| W11 (Fintype) | W25 (Finsupp) | Fintype context needed |
| W11 (Fintype), W03 (FinTuples) | W26 (Matrices) | Matrix is `Fin → Fin → α`; needs funext |
| W15 (BigOpAlgebra) | W21 (BinomialTheorem) | Big-op algebra for binomial theorem |
| W16 (FinsetInduction) | W19 (BinomialCoefficients) | Induction used for choose identities |
