# Coverage Map Final: Finite Mathematics

This is the post-authoring coverage map reflecting the actual state of all 29 worlds
(498 levels total). For each core item from the original coverage-map.md, this records
what actually happened.

## Coverage Stages Key

- **I** = Introduced (first formal encounter, taught with scaffolding)
- **S** = Supported practice (used with hints/coaching)
- **R** = Retrieval (used in pset or later world without scaffolding)
- **G** = Integration (combined with other skills)
- **T** = Transfer (applied in a genuinely new context or surface form)
- **W** = Warning/misconception explicitly addressed

---

## 1. MATH Axis — Core Items

### Fin family

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `Fin n` — type, elements, val | I:W01 S:W02,W03 R:W04 G:W12 T:W29 | I:MeetFin(23L) S:FinNavigation(16L) R:PsetFin(18L) G:CountingTypes T:Finale | **Strong** |
| `Fin.val` and subtype structure | I:W01 S:W02 R:W04 | I:MeetFin L02-L04 S:FinNavigation R:PsetFin | **Strong** |
| `Fin 0` (empty), `Fin 1` (unit) | I:W01 S:W01 R:W04 W:W01 | I:MeetFin L13-L15 W:MeetFin intro R:PsetFin L06 | **Strong** |
| `Fin.castSucc`, `Fin.succ`, `Fin.last` | I:W02 S:W03,W04 R:W04 | I:FinNavigation S:FinTuples R:PsetFin | **Strong** |
| `Fin.cons`, `Fin.snoc` — tuple construction | I:W03 S:W04 R:W12 | I:FinTuples L04-L09 S:FinTuples L10-L16 R:PsetFin | **Strong** |
| `Fin n → α` as tuple | I:W03 S:W04 T:W26 | I:FinTuples L01-L02 S:PsetFin G:Matrices | **Strong** |

### Finset family

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `Finset α` — finite sets | I:W05 S:W06,W07 R:W08 T:W29 | I:FinsetBasics(18L) S:FinsetOps(25L),FinsetImage(23L) R:PsetFinset(14L) T:Finale | **Strong** |
| `Finset.mem`, `Finset.subset` | I:W05 S:W06 R:W08 | I:FinsetBasics S:FinsetOps L05-L07 R:PsetFinset | **Strong** |
| `∅`, `singleton`, `insert` | I:W05 S:W06 R:W08 | I:FinsetBasics L01-L03,L14 S:FinsetOps R:PsetFinset | **Strong** |
| `∪`, `∩`, `\`, `filter` | I:W06 S:W07,W08 R:W08 T:W13,W29 | I:FinsetOps L01-L04 S:FinsetOps L05-L25 R:PsetFinset T:Finale | **Strong** |
| `Finset.image`, `Finset.map` | I:W07 S:W08 R:W09 | I:FinsetImage(23L) S:PsetFinset R:Cardinality. `Finset.map` deferred (noted in PLAN). | **Strong** (image); **Deferred** (map) |
| `Finset.card` — cardinality | I:W09 S:W11,W12 R:W13 T:W23,W29 | I:Cardinality(26L) S:Fintype,CountingTypes R:PsetCardinality T:Finale | **Strong** |
| `Finset.range n` | I:W05 S:W06 R:W08 | I:FinsetBasics L04-L08 S:FinsetOps R:PsetFinset | **Strong** |
| `Finset.powerset`, `powersetCard` | I:W20 S:W22 R:W23 | I:Powerset(27L) S:PascalsTriangle R:PsetCombinatorics | **Strong** |
| `Finset.product` | I:W24 S:W24 R:W29 | I:Products(21L) S:Products R:Finale | **Strong** |
| `Finset.sigma` | I:W24 S:W24 | I:Products L06-L10 S:Products L08-L10 | **Strong** |
| `Finset.diag`, `Finset.offDiag` | I:W24 S:W24 | I:Products L11-L16 S:Products L17-L21 | **Strong** |
| `Finset.disjUnion` | I only | Not covered. Planned as supporting, omitted. | **Not covered** (supporting item, acceptable) |

### Fintype family

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `Fintype α`, `Finset.univ`, `Fintype.card` | I:W11 S:W12 R:W13 T:W27,W29 | I:Fintype(15L) S:CountingTypes(11L) R:PsetCardinality T:CountingTechniques,Finale | **Strong** |
| `card_fin`, `card_prod`, `card_sum` | I:W11 S:W12 R:W13 | I:Fintype L01,L03-L04 S:CountingTypes R:PsetCardinality | **Strong** |
| `card_fun` | I:W11 S:W12 R:W13 | I:Fintype L05 S:CountingTypes L01-L04 R:PsetCardinality L08 | **Strong** |
| `card_congr` (bijective counting) | I:W11 S:W12 R:W13 G:W27 | I:Fintype L11-L13 S:CountingTypes L02 R:PsetCardinality L09-L10 G:CountingTechniques | **Strong** |
| `card_pi` | Supporting | Not covered (only `card_fun` used). | **Not covered** (supporting, acceptable — `card_fun` suffices for the course) |

### Abstraction Ladder

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `List α` — ordered sequences | I:W10 S:W10 R:W13 | I:AbstractionLadder L01-L08 S:L07-L08 R:PsetCardinality L05 | **Strong** |
| `List.Perm` — permutation | I:W10 S:W10 R:W13 T:W29 | I:AbstractionLadder L06-L08 S:L16 R:PsetCardinality | **Strong** |
| `List.Nodup` | I:W10 S:W10 R:W13 | I:AbstractionLadder L12-L13 S:L17,L21 R:PsetCardinality L05 | **Strong** |
| `Multiset α` | I:W10 S:W10 R:W13 | I:AbstractionLadder L09-L11 S:L15 R:PsetCardinality L06 | **Strong** |
| `List.toFinset`, `Multiset.toFinset` | I:W10 S:W10 | I:AbstractionLadder L14-L16 S:L17-L18 | **Strong** |
| List → Multiset → Finset full ladder | I:W10 S:W14 R:W13 T:W29 | I:AbstractionLadder(23L) S:BigOpIntro L12 R:PsetCardinality L05-L06 | **Strong** |

### Big Operators

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `Finset.sum`, `Finset.prod` | I:W14 S:W15 R:W18 T:W21,W29 | I:BigOpIntro(15L) S:BigOpAlgebra(18L) R:PsetBigOp(8L) T:BinomialTheorem,Finale | **Strong** |
| `sum_empty`, `sum_singleton`, `sum_insert` | I:W14 S:W15 R:W18 | I:BigOpIntro L01-L05 S:BigOpAlgebra R:PsetBigOp L01 | **Strong** |
| `sum_congr` | I:W14 S:W15 R:W18 | I:BigOpIntro L08 S:BigOpAlgebra L05 R:PsetBigOp | **Strong** |
| `sum_union`, `sum_filter`, `sum_const` | I:W15 S:W17 R:W18 | I:BigOpAlgebra L03,L06,L07 S:SummationFormulas R:PsetBigOp | **Strong** |
| `sum_add_distrib`, `prod_mul_distrib` | I:W15 S:W17 R:W18 | I:BigOpAlgebra L01-L02 S:SummationFormulas R:PsetBigOp | **Strong** |
| `sum_comm` (double sum) | I:W15 S:W17 R:W18 | I:BigOpAlgebra L08 S:SummationFormulas L13 R:PsetBigOp L04 | **Strong** |
| `sum_range_succ` | Not in original plan | I:BigOpAlgebra L11 S:SummationFormulas R:PsetBigOp | **Strong** (added during implementation) |
| `sum_image`, `prod_image` | Supporting | Not taught as explicit theorems. | **Not covered** (supporting, omitted) |
| `sum_fiberwise` / `card_eq_sum_card_fiberwise` | Supporting | I:CountingTechniques L11 S:L12-L14 R:L16-L17,L19 | **Strong** (promoted from supporting to core during implementation) |

### Combinatorics

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `Nat.factorial` | I:W17 S:W19 R:W23 | I:SummationFormulas L09-L11 S:BinomialCoefficients L09 R:PsetCombinatorics L06 | **Strong** |
| `Nat.choose`, Pascal's identity | I:W19 S:W20,W22 R:W23 T:W29 | I:BinomialCoefficients(16L) S:Powerset,PascalsTriangle R:PsetCombinatorics T:Finale | **Strong** |
| `choose_symm` | I:W19 S:W22 R:W23 | I:BinomialCoefficients L06 S:PascalsTriangle L02,L14 R:PsetCombinatorics L02 | **Strong** |
| `choose_eq_factorial_div_factorial` | I:W19 | I:BinomialCoefficients L09 R:PsetCombinatorics L06 | **Strong** |
| `card_powerset` = 2^n | I:W20 S:W22 R:W23 | I:Powerset L12-L13 S:BinomialTheorem L09 R:PsetCombinatorics | **Strong** |
| `card_powersetCard` → choose | I:W20 S:W22 R:W23 | I:Powerset L17-L18 S:PascalsTriangle R:PsetCombinatorics | **Strong** |
| `add_pow` — binomial theorem | I:W21 S:W22 R:W23 | I:BinomialTheorem(15L) S:PascalsTriangle R:PsetCombinatorics L04 | **Strong** |
| `sum_range_choose` = 2^n | I:W21 S:W22 R:W23 | I:BinomialTheorem L08 S:PascalsTriangle L07 R:PsetCombinatorics | **Strong** |
| `Nat.add_choose_eq` (Vandermonde) | I:W22 S:W22 R:W23 | I:PascalsTriangle L10-L11 S:L12 R:PsetCombinatorics L14 | **Strong** |
| `Finset.Nat.antidiagonal` | I:W22 S:W22 R:W23 | I:PascalsTriangle L03-L06 S:L07-L09 R:PsetCombinatorics L12 | **Strong** |
| Inclusion-exclusion | I:W09 S:W12 R:W13 T:W29 | I:Cardinality L13-L17 S:CountingTypes R:PsetCardinality L02-L03 T:Finale | **Strong** |
| `Nat.descFactorial` | I:W12 S:W12 | I:CountingTypes L05-L07 S:L08-L10 R:PsetCardinality L10 | **Strong** |
| `Nat.ascFactorial` | Supporting | Not covered. | **Not covered** (supporting, acceptable) |
| `Nat.multichoose` | Supporting | Not covered. | **Not covered** (supporting, acceptable) |

### Advanced structures

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `Finsupp α β` | I:W25 S:W25 R:W29 | I:Finsupp(17L) S:Finsupp R:Finale L10 | **Strong** |
| `Finsupp.support`, `single` | I:W25 S:W25 | I:Finsupp L01-L03 S:L05-L07 | **Strong** |
| `Finsupp.mapDomain` | Supporting | Not covered (explicitly noted in world intro as omitted). | **Not covered** (supporting, acceptable) |
| `Matrix m n α` | I:W26 S:W26 R:W29 | I:Matrices(21L) S:Matrices R:Finale L12 | **Strong** |
| `Matrix.diagonal`, `diag`, `transpose` | I:W26 S:W26 | I:Matrices L03,L08-L10 S:L14-L18 | **Strong** |
| `Matrix.ext_iff` | I:W26 S:W26 | I:Matrices L04 S:L05,L07 | **Strong** |

### Counting Techniques

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| Double counting | I:W27 S:W27,W28 R:W28 T:W29 | I:CountingTechniques L11-L14 S:L16-L17 R:PsetCounting L03,L05 T:Finale L09 | **Strong** |
| Pigeonhole | I:W27 S:W27,W28 R:W28 T:W29 | I:CountingTechniques L08-L10 S:L15-L17 R:PsetCounting L02 T:Finale L05-L07 | **Strong** |
| Bijective counting via Equiv | I:W11 S:W12 R:W13 G:W27 T:W29 | I:Fintype L11-L13 S:CountingTypes L02 R:PsetCardinality G:CountingTechniques L01,L04 T:Finale | **Strong** |
| Injection/surjection bounds | I:W27 S:W27 R:W28 | I:CountingTechniques L02-L03 S:L06-L07 R:PsetCounting L03-L04 | **Strong** |

---

## 2. MOVE Axis — Core Proof Strategies

| Move | Planned | Actual | Closure |
|------|---------|--------|---------|
| Unfold definition to expose structure | I:W05 S:W06 R:W08 | I:FinsetBasics S:FinsetOps R:PsetFinset | **Strong** |
| Case split on Fin elements | I:W01 S:W02 R:W04 | I:MeetFin L17-L18 S:FinNavigation L10 R:PsetFin | **Strong** |
| Induction on ℕ for Fin-indexed objects | I:W16 S:W17 R:W18 | I:FinsetInduction S:SummationFormulas R:PsetBigOp | **Strong** |
| Prove set equality by ext | I:W06 S:W07 R:W08 T:W13 | I:FinsetOps L08 S:FinsetImage R:PsetFinset T:PsetCardinality | **Strong** |
| Prove membership by construction | I:W05 S:W06 R:W08 | I:FinsetBasics S:FinsetOps R:PsetFinset | **Strong** |
| Prove non-membership / disjointness | I:W05 S:W06 R:W08 | I:FinsetBasics L11-L12 S:FinsetOps L11 R:PsetFinset | **Strong** |
| Rewrite under a binder (sum_congr) | I:W14 S:W15 R:W18 | I:BigOpIntro L08 S:BigOpAlgebra L05 R:PsetBigOp | **Strong** |
| Split a sum by partition | I:W15 S:W17 R:W18 | I:BigOpAlgebra L06 S:SummationFormulas R:PsetBigOp L02 | **Strong** |
| Telescoping / cancellation | Supporting | I:SummationFormulas L12 S:L14 | **Partial** (introduced, practiced in boss, no retrieval in later world) |
| Double counting / bijective proof | I:W27 S:W27 R:W28 T:W29 | I:CountingTechniques S:L14-L17 R:PsetCounting T:Finale | **Strong** |
| Cardinality via injection/surjection | I:W27 S:W27 R:W28 | I:CountingTechniques L02-L03 S:L06-L07 R:PsetCounting | **Strong** |
| Prove ≤ in both directions | Supporting | I:FinsetOps L07 S:PsetFin L04 R:CountingTechniques L04 | **Strong** |
| Choose element from nonempty finset | I:W05 S:W09 R:W13 | I:FinsetBasics L15-L16 S:Cardinality L03-L04 R:PsetCardinality | **Strong** |
| Pigeonhole argument | Supporting | I:Cardinality L22-L23 S:CountingTechniques L08-L10 R:PsetCounting L02 | **Strong** |
| Induction on Finset.card | Supporting | Not taught as a separate technique. Finset.induction_on used instead. | **Partial** (subsumed by Finset.induction_on) |
| Induction with Finset.insert | I:W16 S:W17 R:W18 T:W23 | I:FinsetInduction(9L) S:SummationFormulas R:PsetBigOp T:PsetCombinatorics | **Strong** |
| Prove big-op identity by induction | I:W16 S:W17 R:W18 T:W23 | I:FinsetInduction S:SummationFormulas R:PsetBigOp T:PsetCombinatorics,Finale | **Strong** |
| Appeal to decidability | Supporting | I:FinsetBasics L17 (decide shortcut) | **Partial** (taught once, not elaborated) |
| Use Equiv to transfer cardinality | Supporting | I:Fintype L11-L13 S:CountingTypes L02 R:PsetCardinality G:CountingTechniques | **Strong** |

---

## 3. LEAN Axis — Tactics and Skills

| Tactic | Plan | Where introduced | Practiced | Closure |
|--------|------|-----------------|-----------|---------|
| `omega` | I:W01 | MeetFin L01 | Throughout course | **Strong** |
| `ext` | I:W06 | MeetFin L15 (earlier than planned) | FinTuples L12, FinsetOps L08, throughout | **Strong** |
| `decide` | I:W05 (re-enable) | FinsetBasics L17 | Throughout | **Strong** |
| `obtain` | I:W04 | PsetFin L08 | Throughout | **Strong** |
| `simp`/`simp_only` | I:W06 | FinsetOps L17 (note: globally disabled, `simp` unlocked here as `simp only` wrapper) | Throughout | **Strong** |
| `by_contra` | Supporting | FinsetOps L19 | Throughout | **Strong** |
| `by_cases` | Supporting | FinsetOps L21 | Throughout | **Strong** |
| `calc` | I:W15 | BigOpAlgebra L14 | SummationFormulas, PsetBigOp L07, throughout | **Strong** |
| `ring` / `ring_nf` | I:W15 | BigOpAlgebra L15 | SummationFormulas, BinomialCoefficients, throughout | **Strong** |
| `induction` (finset context) | I:W16 | FinsetInduction L01 | SummationFormulas, PsetBigOp, BinomialCoefficients | **Strong** |
| `funext` | I:W03 (planned as tactic) | NOT introduced as a separate tactic. Subsumed by `ext`. | N/A | **Acceptable** (ext covers function extensionality) |
| `norm_num` | Core (planned) | NOT introduced — disabled throughout. `omega` used instead. | N/A | **Acceptable** (design choice, `omega` suffices) |
| `congr` / `gcongr` | Supporting | Not formally introduced. | N/A | **Not covered** (supporting) |
| `conv` | Supporting | Not introduced. | N/A | **Not covered** (supporting) |
| `suffices` | Supporting | Not formally introduced. | N/A | **Not covered** (supporting) |
| `refine` | Supporting | Not formally introduced. | N/A | **Not covered** (supporting) |
| `rcases` / `rintro` | Supporting | Not formally introduced (obtain used instead). | N/A | **Acceptable** (obtain covers the use case) |
| `push_neg` | Supporting | CountingTechniques L15 | L16-L17, PsetCounting | **Strong** |
| `contradiction` | Supporting | Not formally introduced (by_contra + exact used). | N/A | **Acceptable** |
| `fin_cases` | Supporting | Not introduced (disabled throughout Phase 1 to force manual case analysis). | N/A | **Acceptable** (design choice) |
| `native_decide` | Supporting | FinsetImage L21 | L21 only | **Partial** (introduced once) |
| `injection` | Not planned | AbstractionLadder L02 | L02 only | **Added** (supporting) |
| `absurd` | Not planned | MeetFin L17 | Throughout | **Added** (supporting) |
| `symm` | Not planned | FinTuples L19 | Throughout | **Added** (supporting) |
| `show`/`change` | Not planned | FinsetOps L16 | Throughout | **Added** (supporting) |
| `subst` | Not planned | CountingTechniques L07 | L07 only | **Added** (supporting) |
| `let` | Not planned | CountingTechniques L14 | L14 only | **Added** (supporting) |

---

## 4. NOTATION Axis

| Item | Plan | Actual | Closure |
|------|------|--------|---------|
| `Fin n` vs `{ i : ℕ // i < n }` | I:W01 W:W01 | I:MeetFin W:MeetFin intro | **Strong** |
| `↑i` vs `i.val` | I:W01 W:W01 | I:MeetFin L02-L04 W:MeetFin intro | **Strong** |
| `⟨k, hk⟩` anonymous constructor | I:W01 S:W01 | I:MeetFin L01 S:throughout | **Strong** |
| `∈` for Finset | I:W05 S:W06 | I:FinsetBasics S:throughout | **Strong** |
| `⊆` for Finset.Subset | I:W06 S:W07 | I:FinsetOps L05-L06 S:throughout | **Strong** |
| `∪`, `∩`, `\` as lattice ops | I:W06 W:W06 | I:FinsetOps L01-L03 W:FinsetOps L16 (lattice notation warning) | **Strong** |
| `{a, b, c}` literal notation | I:W05 S:W06 | I:FinsetBasics L01-L02 S:throughout | **Strong** |
| `∑ x ∈ s, f x` | I:W14 S:W15 | I:BigOpIntro L01 S:throughout | **Strong** |
| `∏ x ∈ s, f x` | I:W14 S:W15 | I:BigOpIntro L06 S:throughout | **Strong** |
| `s ×ˢ t` product notation | Supporting | I:Products L01-L02 | **Strong** |
| `Finset.range n` off-by-one | I:W05 W:W05 | I:FinsetBasics L04-L08 W:FinsetBasics intro | **Strong** |
| `↑s` coercion Finset → Set | Supporting W | Not explicitly taught. | **Not covered** (supporting) |

---

## 5. MISCONCEPTION Axis

| Misconception | Plan | Addressed? | Where |
|---------------|------|-----------|-------|
| `Fin n` starts at 0, not 1 | Core | **Yes** | MeetFin intro, L01 |
| `Finset.range n` is {0,...,n-1} not {0,...,n} | Core | **Yes** | FinsetBasics intro, L04-L08 |
| `Finset` requires `DecidableEq` | Core | **Partial** | Mentioned in intro but not exercised as an error |
| `∪` is `⊔`, `∩` is `⊓` underneath | Core | **Yes** | FinsetOps L16 (LatticeNotation) |
| Multiset ≠ Finset | Core | **Yes** | AbstractionLadder L09-L11 |
| List ≠ Multiset | Core | **Yes** | AbstractionLadder L01-L08 |
| Empty sum = 0, empty product = 1 | Core | **Yes** | BigOpIntro L01-L02, L06, L09 |
| `insert` is idempotent | Supporting | **Yes** | FinsetBasics L14 |
| `Finset.image` can shrink cardinality | Core | **Yes** | FinsetImage L11-L14 |
| `Nat.choose n k = 0` when k > n | Core | **Yes** | BinomialCoefficients L08 |
| `Fin.val` injective but coercion hides proof | Supporting | **Yes** | MeetFin L02-L04 |
| `Matrix` is just a function | Supporting | **Yes** | Matrices L01, intro |
| ℕ has no Fintype instance | Core | **Yes** | Fintype L06 |

---

## 6. EXAMPLE Axis

| Definition | Concrete examples used | Counterexamples | Closure |
|-----------|----------------------|-----------------|---------|
| `Fin n` | Fin 0, Fin 1, Fin 2, Fin 3, Fin 4, Fin 5 | Fin 0 (empty) | **Strong** |
| `Finset` | {1,2,3}, ∅, range 5, univ for Fin 3 | — | **Strong** |
| `Finset.card` | card of literal finsets, card_range | image of non-injective function | **Strong** |
| `Finset.powerset` | powerset {1,2}, powerset {1,2,3} | — | **Strong** |
| `Finset.powersetCard` | powersetCard 2 {1,2,3} | powersetCard too large = ∅ (L23) | **Strong** |
| `Multiset` | Multiset with duplicates | Contrast with finset | **Strong** |
| `List` | [1,2,3] vs [3,1,2] | Same as multiset, different as lists | **Strong** |
| `List.Perm` | [1,2,3] ~ [3,1,2] | — | **Strong** |
| `List.Nodup` | [1,2,3] nodup | [1,2,2,3] not nodup | **Strong** |
| `Fintype` | Fin n, Bool, Fin 2 × Fin 3 | ℕ not Fintype (L06) | **Strong** |
| `Nat.choose` | choose 5 2, choose 4 0, choose 4 4 | choose 3 5 = 0 (L08) | **Strong** |
| `Nat.factorial` | factorial computed concretely | — | **Strong** |
| `Finset.sum` | Concrete sums over small finsets, range | Sum over ∅ = 0 | **Strong** |
| `Finset.prod` | Product over range = factorial | Product over ∅ = 1 | **Strong** |
| `Matrix` | 2×2 matrices, concrete entries | L11: diagonal ∘ diag ≠ identity | **Strong** |
| `Finsupp` | single 3 7, single + single | — | **Strong** |
| `Finset.product` | {1,2} ×ˢ {3,4} concrete | — | **Strong** |
| `add_pow` | (x+y)^2, (x+y)^3 concrete | — | **Strong** |
| `antidiagonal` | antidiagonal 5 concrete | — | **Strong** |
| `Nat.descFactorial` | Concrete computations in CountingTypes | — | **Strong** |

---

## 7. TRANSFER Axis

| Transfer principle | Plan | Actual | Closure |
|-------------------|------|--------|---------|
| "A finite set is determined by membership" — ext | Core | FinsetOps L08, throughout | **Strong** |
| "Count by bijection" | Core | Fintype L11-L13, CountingTechniques L01,L04 | **Strong** |
| "Split a sum, compute parts, add" | Core | BigOpAlgebra L06, SummationFormulas | **Strong** |
| "Prove by induction on number of elements" | Core | FinsetInduction, SummationFormulas | **Strong** |
| "Injective ⟹ |image| = |domain|" | Core | FinsetImage L15-L19, CountingTechniques L02 | **Strong** |
| "Pascal's triangle encodes subset counting" | Core | BinomialCoefficients, Powerset, BinomialTheorem | **Strong** |
| "Double counting" | Core | CountingTechniques L11-L14, SummationFormulas L13 | **Strong** |
| "Pigeonhole principle" | Supporting | Cardinality L22-L23, CountingTechniques L08-L10, Finale L05-L07 | **Strong** |
| "List → Multiset → Finset abstraction" | Core | AbstractionLadder(23L), BigOpIntro L12 | **Strong** |

---

## 8. Level Count Summary

| World | Plan | Actual | Ratio |
|-------|------|--------|-------|
| W01 MeetFin | 7 | 23 | 3.3× |
| W02 FinNavigation | 7 | 16 | 2.3× |
| W03 FinTuples | 7 | 21 | 3.0× |
| W04 PsetFin | 14 | 18 | 1.3× |
| W05 FinsetBasics | 9→18 | 18 | 1.0× |
| W06 FinsetOperations | 10→25 | 25 | 1.0× |
| W07 FinsetImage | 7→23 | 23 | 1.0× |
| W08 PsetFinset | 6→14 | 14 | 1.0× |
| W09 Cardinality | 9→24 | 26 | 1.1× |
| W10 AbstractionLadder | 9 | 23 | 2.6× |
| W11 Fintype | 9 | 15 | 1.7× |
| W12 CountingTypes | 7 | 11 | 1.6× |
| W13 PsetCardinality | 11 | 11 | 1.0× |
| W14 BigOpIntro | 9 | 15 | 1.7× |
| W15 BigOpAlgebra | 10 | 18 | 1.8× |
| W16 FinsetInduction | 7 | 9 | 1.3× |
| W17 SummationFormulas | 6 | 14 | 2.3× |
| W18 PsetBigOp | 6 | 8 | 1.3× |
| W19 BinomialCoefficients | 8 | 16 | 2.0× |
| W20 Powerset | 7 | 27 | 3.9× |
| W21 BinomialTheorem | 7 | 15 | 2.1× |
| W22 PascalsTriangle | 15 | 16 | 1.1× |
| W23 PsetCombinatorics | 6 | 14 | 2.3× |
| W24 Products | 7 | 21 | 3.0× |
| W25 Finsupp | 5 | 17 | 3.4× |
| W26 Matrices | 5 | 21 | 4.2× |
| W27 CountingTechniques | 8 | 19 | 2.4× |
| W28 PsetCounting | 6 | 8 | 1.3× |
| W29 Finale | 6 | 16 | 2.7× |
| **Total** | ~264 | **498** | 1.9× |
