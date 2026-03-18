# Coverage Map: Functions & Relations

**Course**: Sets, functions, relations, equivalences, subtypes, and countability
**Scope** (from long_term.md): The language course for modern mathlib — sets as predicates, images/preimages, restriction to subsets, injective/surjective/bijective-on-a-set maps, relations as sets of pairs, bundled equivalences and partial equivalences, subtypes, countable sets, and encodable types. Teaches the difference between equality, equivalence, and isomorphism. Normalizes working with `↥s`, `Set.MapsTo`, `Set.InjOn`, `Equiv`, and `Encodable`.
**Prerequisites**: NNG4-level Lean fluency. No serious prior mathematics required.
**Status**: Stub (Welcome level only). This map describes what the course SHOULD cover.

---

## 1. Coverage Matrix Summary

### MATH axis

| Item | Importance | Introduce | Supported Practice | Retrieval | Integration | Transfer | Warnings |
|------|-----------|-----------|-------------------|-----------|-------------|----------|----------|
| `Set α` as `α → Prop` | core | W1 | W1, W2 | W3 | throughout | W-transfer | sets≠types |
| `∈` (Set.mem) | core | W1 | W1, W2 | throughout | throughout | W-transfer | — |
| `⊆` (HasSubset) | core | W1 | W1, W3 | W5, W8 | boss levels | W-transfer | ⊆ vs ⊂ |
| `∅` (Set.empty) | core | W1 | W2 | W3 | throughout | — | — |
| `Set.univ` | core | W1 | W2 | W5 | throughout | — | — |
| Set-builder `{x \| P x}` | core | W1 | W1, W2 | throughout | throughout | W-transfer | — |
| `Set.insert`, `Set.singleton` | supporting | W1 | W2 | W-examples | — | — | — |
| `∪` (Set.union) | core | W2 | W2, W3 | W5, W8 | boss levels | W-transfer | — |
| `∩` (Set.inter) | core | W2 | W2, W3 | W5, W8 | boss levels | W-transfer | — |
| `\` (Set.diff) | core | W2 | W2, W3 | W5 | boss levels | — | — |
| `ᶜ` (Set.compl) | core | W2 | W2, W3 | W5 | boss levels | W-transfer | — |
| De Morgan laws for sets | core | W2 | W3 | W5 | boss levels | W-transfer | — |
| Distributive laws (∪/∩) | core | W2 | W3 | W5 | — | — | — |
| `Set.powerset` | supporting | W2 | W3 | — | — | — | — |
| `⋃ i, f i` (Set.iUnion) | core | W4 | W4 | W5 | W-countability | — | — |
| `⋂ i, f i` (Set.iInter) | core | W4 | W4 | W5 | W-countability | — | — |
| `Set.sUnion`, `Set.sInter` | supporting | W4 | W4 | — | — | — | — |
| `Set.prod` | supporting | W4 | W5 | — | — | — | — |
| `Function.Injective` | core | W6 | W6, W8 | W9, W10 | boss levels | W-transfer | — |
| `Function.Surjective` | core | W6 | W6, W8 | W9, W10 | boss levels | W-transfer | — |
| `Function.Bijective` | core | W6 | W6, W8 | W-equiv | boss levels | W-transfer | bij≠Equiv |
| `Function.comp` (∘) | core | W6 | W6, W8 | throughout | boss levels | W-transfer | — |
| `id` | core | W6 | W6 | W8 | — | — | — |
| `Function.LeftInverse` | core | W6 | W6, W8 | W-equiv | boss levels | W-transfer | — |
| `Function.RightInverse` | core | W6 | W6, W8 | W-equiv | boss levels | W-transfer | — |
| `Function.Involutive` | supporting | W6 | W8 | — | — | — | — |
| `Set.image` (f '' S) | core | W7 | W7, W8 | W9, W10 | boss levels | W-transfer | — |
| `Set.preimage` (f ⁻¹' S) | core | W7 | W7, W8 | W9, W10 | boss levels | W-transfer | — |
| `Set.range` | core | W7 | W7, W8 | W10 | boss levels | — | — |
| Image/preimage + set ops | core | W7 | W8 | W10 | boss levels | — | image∩ gotcha |
| `Set.MapsTo` | core | W9 | W9, W10 | W-subtypes | boss levels | W-transfer | — |
| `Set.InjOn` | core | W9 | W9, W10 | — | boss levels | W-transfer | InjOn vs Injective |
| `Set.SurjOn` | core | W9 | W9, W10 | — | boss levels | — | — |
| `Set.BijOn` | core | W9 | W9, W10 | — | boss levels | — | — |
| `Set.restrict` | core | W9 | W10 | W-subtypes | — | — | — |
| `Set.inclusion` | supporting | W9 | W-subtypes | — | — | — | — |
| Binary relation `α → α → Prop` | core | W11 | W11, W13 | throughout | boss levels | W-transfer | — |
| `Reflexive` | core | W11 | W11, W13 | W12 | boss levels | W-transfer | — |
| `Symmetric` | core | W11 | W11, W13 | W12 | boss levels | W-transfer | — |
| `Transitive` | core | W11 | W11, W13 | W12 | boss levels | W-transfer | — |
| `Antisymmetric` | core | W11 | W13 | — | — | — | anti vs a-symmetric |
| `Equivalence` / `IsEquiv` | core | W12 | W12, W13 | W-quotients | boss levels | W-transfer | — |
| Equivalence classes | core | W12 | W12, W13 | W-quotients | boss levels | W-transfer | — |
| Partitions | core | W12 | W12, W13 | — | boss levels | W-transfer | — |
| Partition ↔ equivalence relation | core | W12 | W13 | — | boss levels | W-transfer | — |
| `Setoid` | core | W15 | W15 | W16 | boss levels | — | — |
| `Quotient` | core | W15 | W15, W16 | — | boss levels | W-transfer | — |
| `Quotient.mk` / `⟦·⟧` | core | W15 | W15, W16 | — | boss levels | — | — |
| `Quotient.lift` | core | W15 | W15, W16 | — | boss levels | W-transfer | well-def! |
| `Quotient.ind` | core | W15 | W16 | — | boss levels | — | — |
| `Quotient.sound` | core | W15 | W16 | — | — | — | — |
| `Quotient.exact` | supporting | W15 | W16 | — | — | — | — |
| `Equiv α β` | core | W17 | W17, W18 | — | boss levels | W-transfer | Equiv vs bij |
| `Equiv.refl` | core | W17 | W17 | W18 | — | — | — |
| `Equiv.symm` | core | W17 | W17, W18 | — | boss levels | — | — |
| `Equiv.trans` | core | W17 | W17, W18 | — | boss levels | — | — |
| `Equiv.toFun`, `Equiv.invFun` | core | W17 | W17 | — | — | — | — |
| `Equiv.ofBijective` | core | W17 | W18 | — | boss levels | — | — |
| `Equiv.Perm` | supporting | W17 | W18 | — | — | — | — |
| Equality vs equivalence vs isomorphism | core | W18 | W18 | — | boss levels | W-transfer | central! |
| `Subtype` (`{x : α // P x}`) | core | W19 | W19, W20 | — | boss levels | W-transfer | — |
| `Subtype.val`, `Subtype.property` | core | W19 | W19, W20 | — | — | — | — |
| `Subtype.mk` | core | W19 | W19 | — | — | — | — |
| `↥s` (Set as subtype coercion) | core | W19 | W19, W20 | — | boss levels | — | ↥ syntax |
| `Set.Countable` | core | W21 | W21, W22 | — | boss levels | W-transfer | — |
| `Countable` (typeclass) | core | W21 | W22 | — | — | — | Set vs type |
| `Encodable` | core | W22 | W22 | — | boss levels | — | — |
| `Denumerable` | supporting | W22 | W22 | — | — | — | — |
| Cantor's theorem | core | W21 | — | — | boss | W-transfer | — |
| Schröder-Bernstein | supporting | W22 | — | — | — | W-transfer | — |
| `Set.Finite` | supporting | W21 | — | — | — | — | Finite vs Countable |

### MOVE axis

| Move | Importance | Introduce | Supported Practice | Retrieval | Integration | Transfer |
|------|-----------|-----------|-------------------|-----------|-------------|----------|
| Set extensionality: prove A = B by ∀ x, x ∈ A ↔ x ∈ B | core | W1 | W2, W3 | W5 | boss levels | W-transfer |
| Double inclusion: A ⊆ B ∧ B ⊆ A | core | W1 | W2, W3 | W5 | boss levels | W-transfer |
| Membership chasing through set operations | core | W2 | W2, W3 | W5, W7 | boss levels | — |
| Unfolding a definition to expose its quantifier structure | core | W1 | W6, W11 | throughout | boss levels | W-transfer |
| Exhibiting a witness for ∃ | core | W6 (surj) | W7, W12 | throughout | boss levels | W-transfer |
| Exhibiting a preimage for image membership | core | W7 | W7, W8 | W10 | boss levels | — |
| Specializing a universal hypothesis | core | W1 (⊆) | W4, W6 | throughout | boss levels | W-transfer |
| Composing implications | core | W6 (inj∘inj) | W6, W8 | W10 | boss levels | — |
| Constructing an inverse function | core | W6 | W17 | W18 | boss levels | W-transfer |
| Proof by contradiction | core | W6 (inj) | W11, W21 | — | boss levels | W-transfer |
| Proof by contrapositive | supporting | W6 | W8 | — | — | W-transfer |
| Case splitting on ∨ / union membership | core | W2 | W3, W4 | W5 | boss levels | — |
| Working with ↔ (splitting, using each direction) | core | W1 | W2, W12 | throughout | boss levels | — |
| Proving well-definedness of quotient maps | core | W15 | W15, W16 | — | boss levels | W-transfer |
| Diagonalization argument | core | W21 | — | — | boss | W-transfer |
| Using function extensionality (funext) | core | W6 | W17 | — | — | — |
| Constructing an equivalence relation from scratch | core | W12 | W13 | W15 | boss levels | W-transfer |
| Using antisymmetry (≤ in both directions → =) | supporting | W11 | W13 | — | — | W-transfer |
| Building a function from cases | supporting | W6 | W9 | — | — | — |
| Induction on ℕ for countability | supporting | W21 | W22 | — | — | — |

### LEAN axis

| Item | Importance | Introduce | Supported Practice | Retrieval | Integration |
|------|-----------|-----------|-------------------|-----------|-------------|
| `ext` (set extensionality) | core | W1 | W2, W3 | W5 | boss levels |
| `simp` with set simp lemmas | core | W2 | W3, W5 | throughout | boss levels |
| `push_neg` | core | W2 (compl) | W6 | W11 | boss levels |
| `use` (existential witness) | core | W6 | W7, W12 | throughout | boss levels |
| `obtain ⟨a, ha, rfl⟩` (destructuring) | core | W7 | W7, W8 | throughout | boss levels |
| `rintro ⟨⟩` (pattern-matching intro) | core | W2 | W7, W8 | throughout | boss levels |
| `constructor` (for ∧ and ↔) | core | W1 | W2, W12 | throughout | boss levels |
| `change` (rewriting goal to definitional equal) | core | W1 | W6, W11 | throughout | — |
| `unfold` | supporting | W1 | W6 | — | — |
| `show` | supporting | W1 | W6 | — | — |
| `specialize` | core | W1 | W4, W6 | throughout | boss levels |
| `have` (intermediate claims) | core | W6 | W7, W11 | throughout | boss levels |
| `funext` | core | W6 | W17 | — | — |
| `congr` / `congr_arg` | supporting | W6 | W7 | — | — |
| `calc` blocks | supporting | W11 (trans) | W12 | — | — |
| `left` / `right` | core | W2 | W3, W7 | throughout | — |
| `rcases` / `obtain` | core | W2 | throughout | throughout | boss levels |
| `exists_prop` usage | supporting | W7 | W8 | — | — |
| `mem_image` / `mem_preimage` lemma usage | core | W7 | W7, W8 | W10 | boss levels |
| `Quotient.lift` / `Quotient.mk` usage | core | W15 | W16 | — | boss levels |
| `Equiv.mk` construction | core | W17 | W18 | — | boss levels |
| `Subtype.mk` / `⟨val, property⟩` | core | W19 | W20 | — | boss levels |
| Anonymous constructor `⟨ , ⟩` | core | W1 | throughout | throughout | boss levels |
| `tauto` (disabled when teaching logic) | — | — | — | — | disable early |
| `decide` (disabled) | — | — | — | — | disable |
| `simp_all` (disabled) | — | — | — | — | disable |

### NOTATION axis

| Item | Importance | Introduce | Notes |
|------|-----------|-----------|-------|
| `∈`, `∉` | core | W1 | Standard membership |
| `⊆`, `⊂` | core | W1 | Distinguish ⊆ from ⊂ |
| `∪`, `∩` | core | W2 | — |
| `\` (set diff) | core | W2 | Not minus; not backslash |
| `ᶜ` (complement) | core | W2 | Typed as `\compl` or `ᶜ` |
| `{x \| P x}` | core | W1 | Set-builder; `\|` vs `\mid` |
| `{a, b, c}` | supporting | W-examples | Finite set literal |
| `''` for `Set.image` | core | W7 | Two single quotes, easy to miss |
| `⁻¹'` for `Set.preimage` | core | W7 | Superscript notation |
| `∘` for composition | core | W6 | `\circ` |
| `⋃ i, f i` / `⋂ i, f i` | core | W4 | Indexed union/inter |
| `⟦x⟧` for `Quotient.mk` | core | W15 | `\[[` and `\]]` |
| `≃` for `Equiv` | core | W17 | `\simeq` |
| `↑` (coercion up-arrow) | core | W19 | Subtype to parent type |
| `↥s` (set-to-subtype coercion) | core | W19 | Often invisible in goals |
| `Set.Elem s` | core | W19 | Type of elements of s |
| `Subtype.val` vs `↑` | core | W19 | Two ways to coerce down |

### MISCONCEPTION axis

| Misconception | Importance | Where to address | How |
|---------------|-----------|-----------------|-----|
| Sets are types (they are not — `Set α` is `α → Prop`) | core | W1 | Explicit intro level; revisit in W19 |
| `f '' (A ∩ B) = f '' A ∩ f '' B` (false without injectivity) | core | W7 or W-examples | Counterexample level |
| `f '' (A ∪ B) = f '' A ∪ f '' B` (true) vs intersection (false) | core | W7 | Side-by-side levels |
| Bijective = Equiv (no — bijective is Prop, Equiv carries data) | core | W17 | Explicit comparison level |
| Quotient.lift "just works" (no — needs well-definedness proof) | core | W15 | Level where well-def fails first |
| ⊆ and ⊂ confusion | supporting | W1 | Warning in docstring |
| Equivalence relation ≠ Equiv (completely different concepts) | core | W17 | Explicit naming level |
| Complement is `ᶜ` not `-` or `~` | supporting | W2 | Notation doc |
| `Set.image` notation `''` easy to confuse with string quotes | supporting | W7 | Doc warning |
| Countable includes finite (some students think countable = countably infinite) | core | W21 | Explicit level |
| A relation that is symmetric+transitive is reflexive (false — empty relation) | core | W11 or W-examples | Counterexample level |
| `Set.restrict` changes the codomain (it doesn't — only domain) | supporting | W9 | Warning in docstring |
| Antisymmetric ≠ not-symmetric | supporting | W11 | Warning in docstring; counterexample |
| Image of a subset vs image restricted to a subset | supporting | W9 | Comparison level |

### TRANSFER axis

| Transfer item | Importance | Where |
|---------------|-----------|-------|
| "To show two sets are equal, show each is contained in the other" | core | W1 conclusion, W-transfer |
| "To show x ∈ f(S), find a ∈ S with f(a) = x" | core | W7 conclusion, W-transfer |
| "Injective: different inputs → different outputs. Prove: assume f(a) = f(b), show a = b" | core | W6 conclusion, W-transfer |
| "Surjective: every output has an input. Prove: given y, construct x with f(x) = y" | core | W6 conclusion, W-transfer |
| "An equivalence relation partitions a set into non-overlapping classes" | core | W12 conclusion, W-transfer |
| "A quotient map must be well-defined: equivalent inputs must give equal outputs" | core | W15 conclusion, W-transfer |
| "A bijection and its inverse are two halves of the same structure" | core | W17 conclusion, W-transfer |
| "Countability means there's an injection into ℕ or a surjection from ℕ" | core | W21 conclusion, W-transfer |
| "Cantor: no function from a set to its power set is surjective — proved by diagonalization" | core | W21 conclusion, W-transfer |
| "Subtypes restrict attention to elements satisfying a property — like working 'inside a set'" | core | W19 conclusion, W-transfer |

### EXAMPLE axis

| Example | Type | Where | Purpose |
|---------|------|-------|---------|
| Evens = {n : ℕ \| Even n}, Odds | concretization | W1 or W-examples | First concrete set |
| Primes as a set | concretization | W1 or W-examples | Set-builder with a predicate |
| {1, 2, 3} ∩ {2, 3, 4} = {2, 3} | concretization | W2 or W-examples | Concrete intersection |
| Complement of evens = odds | concretization | W2 or W-examples | Concrete complement |
| (· + 1) on ℕ: injective, not surjective | concretization + counterexample | W6 or W-examples | Injective non-surjection |
| (· / 2) or (fun n ↦ n / 2) on ℕ: surjective (onto range), not injective | concretization + counterexample | W6 or W-examples | Surjective non-injection |
| Negation on ℤ: bijective involution | concretization | W6 or W-examples | Concrete bijection |
| Image of evens under (· * 2) | concretization | W7 or W-examples | Image computation |
| f '' (A ∩ B) ≠ f '' A ∩ f '' B: concrete counterexample | counterexample | W7 or W-examples | Critical misconception |
| Congruence mod n as equivalence relation | concretization | W12 or W-examples | Standard equiv relation |
| "Same parity" as equivalence relation on ℕ | concretization | W12 or W-examples | Simple equiv relation |
| Counterexample: symmetric+transitive but not reflexive (empty relation on {0}) | counterexample | W11 or W-examples | Critical misconception |
| Counterexample: relation that is reflexive+symmetric but not transitive | counterexample | W11 or W-examples | Relation properties are independent |
| ℤ/nℤ as a quotient | concretization | W15 or W-examples | Standard quotient |
| Fin n ≃ {i : ℕ // i < n} | concretization | W17 or W-examples | Concrete Equiv |
| Even numbers as subtype {n : ℕ // Even n} | concretization | W19 or W-examples | Concrete subtype |
| ℕ is countable, ℝ is not | concretization | W21 or W-examples | Countability |
| ℕ × ℕ is countable (pairing function) | concretization | W22 or W-examples | Countability construction |
| Cantor diagonal on Bool-valued functions | concretization | W21 | Diagonalization |
| Antisymmetric but not symmetric: ≤ on ℕ | concretization | W11 or W-examples | Distinguishing anti- from a- |

---

## 2. Core Uncovered Items

Since the course is currently a stub, EVERYTHING is uncovered. The following are the items that absolutely must be covered and should be tracked carefully during authoring:

1. **Set extensionality as a proof move** — This is the single most important proof technique in the course. It must be introduced early, practiced heavily, and transferred.

2. **Image/preimage asymmetry** — The fact that preimage commutes with all set operations but image does not (specifically image does not distribute over intersection without injectivity) is a core insight. It needs both positive and negative coverage.

3. **Quotient well-definedness** — The requirement that quotient maps respect the equivalence relation is the central difficulty of working with quotients. It must have dedicated levels, not be a footnote.

4. **The equality/equivalence/isomorphism distinction** — This is explicitly called out in the course description. It deserves a dedicated world or at minimum a substantial cluster of levels.

5. **Subtype coercion mechanics** — Working with `↥s`, `Subtype.val`, `↑`, `Subtype.property` is a practical Lean skill that many courses need. It must be thoroughly taught.

6. **Cantor's theorem and diagonalization** — The course includes countability, and Cantor's theorem is the most important result. The diagonalization argument is a proof move that transfers broadly.

7. **Encodable** — Explicitly in scope. Must be covered, not just mentioned.

8. **Partial equivalence relations** — Explicitly in scope. Less common pedagogically but required.

9. **`Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`** — Explicitly in scope. These are the "on a set" variants that mathlib uses heavily. Must be distinguished from the plain `Injective`/`Surjective`/`Bijective`.

---

## 3. Weakly Covered Items

(These are items at risk of being covered in name only, without full closure.)

1. **Indexed unions/intersections** — Easy to introduce but hard to practice meaningfully. Without concrete mathematical applications, `⋃ i, f i` levels risk being pure syntax exercises. Need application in countability proofs.

2. **`Set.restrict` and `Set.inclusion`** — Supporting items that are easy to skip but matter for later courses (topology, analysis). Need at least introduction + one practice level.

3. **`Function.Involutive`** — Supporting, but useful for concrete bijection examples (negation on ℤ). Risk of being mentioned in docs but never practiced.

4. **Partition ↔ equivalence relation correspondence** — Mathematically important but easy to cover only in one direction. Both directions need levels.

5. **`Quotient.ind` / `Quotient.rec`** — The induction principle for quotients. Easy to skip in favor of `Quotient.lift`, but important for some proofs.

6. **`Equiv.Perm`** — Permutations as self-equivalences. Supporting, but connects to later group theory. Risk of being omitted.

7. **`Denumerable`** — The countably-infinite variant of Encodable. Easy to conflate with or skip relative to `Encodable`.

8. **`Antisymmetric`** — Taught in the relations world but may never be retrieved or integrated, since the course doesn't go deep into order theory.

9. **Schröder-Bernstein** — In scope as a supporting theorem. Complex proof. Risk of being either too hard for a level or too hand-wavy.

---

## 4. Example Coverage Gaps

Since the course is a stub, all examples are gaps. The following are the most critical concrete examples that MUST appear:

### Definitions that must be concretized (not just used abstractly)

| Definition | Required concrete example | Gap if missing |
|-----------|--------------------------|----------------|
| Set membership | Evens, odds, or primes as specific sets of ℕ | Learner never computes ∈ for a specific predicate |
| Set operations | {1,2,3} ∪ {2,3,4}, {1,2,3} ∩ {2,3,4}, etc. | Learner never verifies set algebra on specific sets |
| Injective | (· + 1) on ℕ | Learner cannot identify injectivity in a concrete function |
| Surjective | A concrete surjection (e.g., Int.natAbs or a mod function) | Same |
| Not injective | A concrete non-injection with specific counterexample | Learner never constructs a counterexample to injectivity |
| Not surjective | (· + 1) on ℕ (0 has no preimage) | Same for surjectivity |
| Image | Image of a specific set under a specific function | Learner never computes f '' S concretely |
| Image/inter failure | Specific f, A, B where f '' (A ∩ B) ≠ f '' A ∩ f '' B | Most important counterexample in the course |
| Equivalence relation | Congruence mod 2 (or mod n) on ℤ | Learner never verifies reflexivity/symmetry/transitivity for a specific relation |
| Not an equivalence relation | Specific relation failing one axiom | Learner cannot diagnose why a relation fails |
| Equivalence classes | Classes of mod 2 on ℤ | Learner never computes a specific class |
| Quotient | ℤ / (mod 2) or similar | Learner never works with a specific quotient |
| Equiv | Fin n ≃ {i : ℕ // i < n}, or Bool ≃ Fin 2 | Learner never constructs a specific Equiv |
| Subtype | {n : ℕ // Even n} or {n : ℕ // n < 5} | Learner never works with a specific subtype |
| Countable | ℕ × ℕ is countable | Learner never constructs a countability proof |
| Uncountable | No surjection ℕ → Set ℕ (Cantor) | Learner never sees uncountability |

### Missing counterexamples (critical)

| Statement to disprove | Required counterexample |
|----------------------|------------------------|
| Symmetric + transitive → reflexive | Empty relation on a nonempty type |
| Image distributes over intersection | Constant function, two disjoint sets |
| Surjective ∘ injective is bijective (order matters) | Specific composition that fails |
| Every injective function has a left inverse (constructively) | On empty domain edge case or non-constructive note |

---

## 5. Redundant Items

Since the course is a stub, there is no current redundancy. However, the following are **redundancy risks** during authoring:

1. **Set algebra drill** — There are many set identities (de Morgan, distributive, absorption, etc.). It is easy to create 10+ levels that all reduce to "apply ext, split the iff, chase membership." After 4-5 such levels, additional ones teach nothing new. The set operations world must cap pure-algebra levels and move to application.

2. **Injective/surjective symmetry** — The proofs for "composition of injectives is injective" and "composition of surjectives is surjective" use the same shape. Doing both is fine; doing both twice (once for types, once for sets) without new demand is redundant.

3. **Multiple equivalence relation examples** — Mod 2, mod 3, mod n, same-parity, same-sign... After 2-3 equivalence relation verifications, the proof shape is learned. Additional examples should introduce new demand (e.g., verifying on a non-obvious relation, or one that is NOT an equivalence relation).

4. **Subtype coercion levels** — Coercion mechanics can generate many levels that all reduce to "apply Subtype.val" or "use ⟨x, hx⟩". Cap these.

---

## 6. Granularity Defects

Since there is no authored content, these are **predicted granularity defects** based on the subject matter:

### Predicted overbroad levels

1. **"Prove that the composition of two bijections is a bijection"** — This requires: unfolding Bijective into Injective ∧ Surjective, proving both, each of which requires its own subproof. Should be a boss, not a regular level, and must come AFTER separate levels on inj∘inj and surj∘surj.

2. **"Prove that equivalence classes partition the set"** — This requires: showing classes are nonempty, showing classes are disjoint, showing the union covers everything. At least 2-3 levels.

3. **"Construct an Equiv from a bijection"** — Requires: constructing the inverse, proving left-inverse, proving right-inverse, assembling the Equiv. Multiple moves.

4. **"Prove Cantor's theorem"** — The diagonalization argument requires: defining the diagonal set, assuming surjectivity, deriving contradiction. Each step is a separate move.

5. **"Prove the partition/equivalence-relation correspondence"** — Two directions, each multi-step. Must be split.

### Predicted overfine levels

1. **Individual set identity levels beyond 4-5** — After the learner has done union commutativity, intersection commutativity, de Morgan, and distributivity, additional identities like absorption or double complement are diminishing returns unless they introduce a new move.

2. **Separate levels for `Set.mem_union` and `Set.mem_inter`** — These are one-liner unfoldings. They should be folded into the first level that uses union/intersection, not standalone.

3. **Separate levels for `Equiv.refl`, `Equiv.symm`, `Equiv.trans`** — Each is trivial on its own. Better to teach them in context within an Equiv construction level.

### Predicted worlds that should be split

1. **"Functions" as a single world** — The injective/surjective/bijective material alone is one world; image/preimage is another; functions-on-sets (MapsTo/InjOn) is a third. Three distinct centers of gravity.

2. **"Relations and Equivalences" as a single world** — Binary relations are one world; equivalence relations and partitions are another.

3. **"Countability and Encodability" as a single world** — Countability (Set.Countable, Cantor) is one center of gravity; Encodable/Denumerable is another.

### Predicted worlds that should be merged

1. **`Set.prod` as its own world** — Not enough material. Should be a few levels within the indexed families world or the set operations world.

2. **Partial equivalence relations as their own world** — Not enough material for a full world. Should be a subsection of the relations or equivalences world.

---

## 7. Novelty Hotspots

The following are places where too much novelty would concentrate if not carefully managed:

### Hotspot 1: Image/Preimage world (W7)
- New math: Set.image, Set.preimage, Set.range
- New notation: `''`, `⁻¹'`
- New proof move: exhibiting preimages, destructuring image membership
- New Lean: `obtain ⟨a, ha, rfl⟩`, `mem_image`, `mem_preimage`

**Mitigation**: Split notation introduction from proof-move introduction. First level: what `''` and `⁻¹'` mean (trivial proofs). Second level: how to prove membership in an image (the real move). Third level: practice.

### Hotspot 2: Quotients world (W15)
- New math: Setoid, Quotient, equivalence classes as a type
- New notation: `⟦·⟧`
- New proof move: well-definedness proofs
- New Lean: `Quotient.mk`, `Quotient.lift`, `Quotient.ind`, `Quotient.sound`

**Mitigation**: Start with Setoid construction (familiar from W12). Then introduce Quotient.mk notation. Then Quotient.lift with well-definedness as the main move. Then Quotient.ind. Multiple levels, each with one new element.

### Hotspot 3: Subtypes world (W19)
- New math: Subtype, set-subtype correspondence
- New notation: `↥s`, `↑`, `{x // P x}`
- New Lean: `Subtype.mk`, `Subtype.val`, `Subtype.property`, coercion tactics

**Mitigation**: Introduce Subtype syntax first with trivial proofs. Then coercion mechanics. Then the correspondence between Set.Elem and Subtype. Keep each level to one notation issue or one coercion pattern.

### Hotspot 4: Functions-on-sets world (W9)
- New math: MapsTo, InjOn, SurjOn, BijOn, restrict
- New proof move: restricting global properties to sets
- Subtle distinction: InjOn vs Injective

**Mitigation**: Introduce MapsTo first (simplest). Then InjOn as the key concept. SurjOn and BijOn follow the same pattern. Restrict can come last. The InjOn-vs-Injective distinction deserves a dedicated level.

### Hotspot 5: First set operations world (W2)
- New math: union, intersection, complement, difference
- New notation: `∪`, `∩`, `\`, `ᶜ`
- New tactic: `ext` for set extensionality

**Mitigation**: The `ext` tactic is the dominant lesson of the first level. Union and intersection can share a level if the proofs are symmetric. Complement introduces `push_neg` which is a new tactic — needs its own level. De Morgan needs `ext` + complement reasoning, so it should come after both.

---

## 8. Recommended Splits/Merges

### Recommended splits

1. **Split "Functions" into three worlds:**
   - W6: Function properties (injective, surjective, bijective, composition, inverses)
   - W7: Image and preimage (Set.image, Set.preimage, interactions with set ops)
   - W9: Functions on sets (MapsTo, InjOn, SurjOn, BijOn, restrict)

2. **Split "Relations" into two worlds:**
   - W11: Binary relations (reflexive, symmetric, transitive, antisymmetric, closures)
   - W12: Equivalence relations and partitions (equivalence, classes, partition correspondence)

3. **Split "Countability" into two worlds:**
   - W21: Countability and Cantor (Set.Countable, Countable, Cantor's theorem, uncountability)
   - W22: Encodability (Encodable, Denumerable, concrete encodings)

4. **Split "Quotients and Equivalences" into at least two worlds:**
   - W15: Quotients (Setoid, Quotient, mk, lift, ind, sound)
   - W17: Equiv (Equiv type, construction, properties, ofBijective)

### Recommended merges

1. **Merge partial equivalence relations into the relations cluster** — not enough material for a standalone world. Cover in 1-2 levels within W11 or W12.

2. **Merge `Set.prod` into the indexed families world (W4)** — 1-2 levels, not a world.

3. **Merge `Function.Involutive` into the functions world (W6)** — 1 level showing involutions are bijective.

---

## 9. Recommended New Levels or New Worlds

### Recommended worlds (proposed full structure)

**Cluster 1: Sets (W1-W5)**

| World | Center of Gravity | Levels (est.) |
|-------|-------------------|---------------|
| W1: Sets and Membership | Set α, ∈, ⊆, set-builder, ext, double inclusion | 8-10 |
| W2: Set Operations | ∪, ∩, \, ᶜ, de Morgan, distributive laws | 8-10 |
| W3: Sets Pset | Transfer/retrieval on sets material, reduced scaffolding | 6-8 |
| W4: Indexed Families | ⋃, ⋂, sUnion, sInter, Set.prod | 6-8 |
| W5: Concrete Sets | Example world: specific sets, computations, counterexamples | 6-8 |

**Cluster 2: Functions (W6-W10)**

| World | Center of Gravity | Levels (est.) |
|-------|-------------------|---------------|
| W6: Function Properties | Injective, surjective, bijective, composition, inverses | 8-10 |
| W7: Image and Preimage | Set.image, Set.preimage, Set.range, interaction with set ops | 8-10 |
| W8: Functions Pset | Transfer/retrieval on functions material | 6-8 |
| W9: Functions on Sets | MapsTo, InjOn, SurjOn, BijOn, restrict | 8-10 |
| W10: Concrete Functions | Example world: specific functions, image computations, counterexamples | 6-8 |

**Cluster 3: Relations (W11-W14)**

| World | Center of Gravity | Levels (est.) |
|-------|-------------------|---------------|
| W11: Binary Relations | Relations as Prop-valued, reflexive, symmetric, transitive, antisymmetric | 8-10 |
| W12: Equivalence Relations | Equivalence, classes, partitions, correspondence | 8-10 |
| W13: Relations Pset | Transfer/retrieval, mixed relation problems | 6-8 |
| W14: Concrete Relations | Example world: mod n, parity, specific (non-)equivalence relations | 6-8 |

**Cluster 4: Quotients and Equivalences (W15-W18)**

| World | Center of Gravity | Levels (est.) |
|-------|-------------------|---------------|
| W15: Quotients | Setoid, Quotient, mk, lift (well-def!), ind, sound | 8-10 |
| W16: Quotients Pset | Transfer/retrieval on quotient material | 6-8 |
| W17: Equiv | Equiv type, refl/symm/trans, construction, ofBijective, Perm | 8-10 |
| W18: Equality, Equivalence, Isomorphism | The three concepts compared; when to use which; review/integration | 6-8 |

**Cluster 5: Subtypes and Countability (W19-W22)**

| World | Center of Gravity | Levels (est.) |
|-------|-------------------|---------------|
| W19: Subtypes | Subtype, val, property, mk, ↥s, coercions | 8-10 |
| W20: Subtypes Pset | Transfer/retrieval; connection to sets and functions | 6-8 |
| W21: Countability | Set.Countable, Countable, Cantor's theorem, diagonalization | 8-10 |
| W22: Encodability | Encodable, Denumerable, concrete encodings, Schröder-Bernstein | 8-10 |

**Total**: 22 worlds, ~170-190 levels estimated.

### Recommended example/counterexample levels (within example worlds)

W5 (Concrete Sets):
- L1: Verify 3 ∈ {n : ℕ | n > 2}
- L2: Verify {1,2} ⊆ {1,2,3}
- L3: Compute {1,2,3} ∩ {2,3,4}
- L4: Verify complement of evens = odds (or a finite version)
- L5: De Morgan on specific sets
- L6: Counterexample: A ⊂ B does not mean A = B (construct specific sets)
- Boss: Multi-step set computation

W10 (Concrete Functions):
- L1: Verify (· + 1) on ℕ is injective
- L2: Show (· + 1) on ℕ is not surjective (0 has no preimage)
- L3: Verify (· * 2) is injective
- L4: Compute the image of {1,2,3} under some function
- L5: Counterexample: f '' (A ∩ B) ≠ f '' A ∩ f '' B with specific f, A, B
- L6: Construct a concrete left inverse
- Boss: Build a bijection between two specific types and verify properties

W14 (Concrete Relations):
- L1: Verify mod 2 is reflexive
- L2: Verify mod 2 is symmetric
- L3: Verify mod 2 is transitive
- L4: Counterexample: a symmetric, transitive relation that isn't reflexive
- L5: Counterexample: a reflexive, symmetric relation that isn't transitive
- L6: Compute equivalence classes of mod 2 on a finite set
- Boss: Verify a non-trivial relation is/isn't an equivalence relation

### Recommended additional levels (not world-sized)

- **Level on `Set.powerset`**: 1-2 levels in W2 or W4. Powerset is a set of sets; connects to Cantor later.
- **Level on partial equivalence relations**: 1-2 levels in W11 or W12. Required by scope.
- **Level on `Equiv.Perm`**: 1-2 levels in W17. Connects to later group theory course.
- **Level on Schröder-Bernstein**: 2-3 levels in W22. Either prove it (hard) or use it as a tool.

---

## 10. Items That Should Be Demoted, Delayed, or Hidden in the Inventory

### Demoted to supporting/optional

| Item | Reason |
|------|--------|
| `Set.sUnion`, `Set.sInter` | Less commonly used than indexed variants; teach but don't emphasize |
| `Set.powerset` | Useful for Cantor but not core to daily mathlib use |
| `Function.Involutive` | Niche; cover as one level, not a world theme |
| `Set.prod` | Supporting; a few levels within indexed families |
| `Equiv.Perm` | Important for group theory but not core to this course |
| `Denumerable` | Supporting variant of Encodable |
| Schröder-Bernstein | Beautiful but complex; supporting, not core |

### Delayed (should appear late in the course)

| Item | Reason |
|------|--------|
| `Quotient.ind` / `Quotient.rec` | Requires comfort with quotients first; introduce after Quotient.lift |
| `Equiv.ofBijective` | Requires understanding of both Equiv and Bijective |
| `Encodable` | Requires understanding of countability |
| Cantor's theorem | Requires diagonalization proof move; needs all earlier set/function material |
| Equality/equivalence/isomorphism distinction | Requires having seen all three concepts |

### Hidden in inventory until needed

| Item | Hide until |
|------|-----------|
| `simp` set lemmas (many low-level lemmas) | Always available but don't clutter early inventory |
| `Set.mem_union_iff`, `Set.mem_inter_iff`, etc. | Available but use `simp` or `change` instead when teaching |
| `Quotient.exact` | After Quotient.sound is learned |
| Lattice-level set operations (`sup`, `inf`) | These are aliases for ∪/∩ via lattice structure — MUST be disabled or they bypass set-level reasoning |

### Exploit vectors to disable

Based on lessons learned from other courses:

| Tactic/Theorem | Why disable |
|----------------|-------------|
| `trivial` | Closes trivially true goals without learning |
| `decide` | Closes decidable goals without learning |
| `simp` (globally) | Solves too many set goals; enable only when teaching simp |
| `aesop` | Solves many membership/extensionality goals |
| `simp_all` | Even more powerful than simp |
| `tauto` | Closes propositional goals (set theory is propositional) |
| `norm_num` | Less relevant here but still an exploit |
| `ext` (early) | Should be TAUGHT, not available from the start; introduce in W1 |
| `Set.ext_iff` | Same — teach, then enable |
| Lattice lemmas (`sup_comm`, `inf_comm`, etc.) | Set ∪/∩ are lattice operations; lattice lemmas one-shot set identities |
| `Set.subset_antisymm` | Should be earned, not free |

---

## 11. Confidence Notes

### High confidence

- **Coverage scope**: The course description in long_term.md is explicit. The 7 axes above cover it fully.
- **Proof move decomposition**: The proof moves for sets, functions, and relations are well-understood and standard.
- **Example coverage**: The concrete examples listed are standard pedagogical choices.
- **Novelty hotspots**: Image/preimage and quotients are known difficulty spikes in this material.
- **Granularity risks**: The predicted overbroad levels (bijection composition, partition correspondence, Cantor) are standard complexity points.

### Medium confidence

- **World count (22 worlds)**: This is a large course. The actual count depends on how much material each world needs and whether some worlds can be tighter. The course architect may adjust.
- **Encodable/Denumerable depth**: I'm confident these should be covered but less certain about how many levels they warrant. Depends on what mathlib API is available at the right level of abstraction for a basic course.
- **Schröder-Bernstein inclusion**: Supporting, but the proof is long. It might be better as a stated-and-used theorem rather than a proved-from-scratch result. Course architect should decide.
- **Partial equivalence relations**: Required by scope but pedagogically niche. May deserve only 1-2 levels.

### Low confidence

- **Specific level counts per world**: The 8-10 / 6-8 estimates are rough. Actual counts depend on how finely proof moves decompose for each topic, which only becomes clear during authoring.
- **Whether `Set.restrict` and `Set.inclusion` need dedicated levels** vs. being covered as part of MapsTo/InjOn levels: depends on how mathlib's API actually works in practice at these theorems.
- **Whether Cantor's theorem is feasible as a student proof** or should be a stated/used result: the diagonalization argument is beautiful but may be too complex for a basic course. Needs investigation during authoring.
- **Exact exploit surface**: The lattice-alias exploit vector (from orders_lattices lessons learned) applies here because Set is a lattice. I've flagged it but the exact list of theorems to disable will need to be discovered during playtesting.
