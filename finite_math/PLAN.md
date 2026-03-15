# Course Architecture: finite_math

## 1. Course promise

By the end of this course, the learner will be able to:

- Construct and reason about finite index types (`Fin n`), finite sets (`Finset`), lists, and multisets in Lean 4 / mathlib.
- Count elements of finite types using `Fintype.card` and derive cardinality results for compound types.
- Write and manipulate big-operator expressions (`Finset.sum`, `Finset.prod`) including inductive proofs, splitting, filtering, and reindexing.
- Prove binomial coefficient identities, apply Pascal's rule, and state the binomial theorem.
- Apply the pigeonhole principle and inclusion-exclusion as proof moves.
- Work with finitely supported functions and see matrices as functions over finite index types.
- Transfer all of the above to ordinary paper-proof reasoning: state what "finite" means, write sigma-notation arguments, and articulate counting proofs in plain English.

## 2. Learner profile

- **Prerequisites**: NNG4-level Lean fluency. The learner can read goal states, use `rw`, `exact`, `apply`, `intro`, `cases`, `constructor`, `have`, `use`, and `assumption`. They understand natural-number induction.
- **No serious mathematical prerequisites** beyond basic arithmetic and familiarity with the concept of a set.
- **Expected pace**: This is a basic course. Expect a learner to spend 15--30 hours across all worlds.

## 3. Four prerequisite maps

### 3a. Content map (MATH)

| ID | Item | Role |
|----|------|------|
| M1 | `Fin n` as `{ i : Nat // i < n }` | core definition |
| M2 | `Fin.val`, `Fin.mk`, `Fin.last`, `Fin.castSucc`, `Fin.succ` | constructors/navigation |
| M3 | `Fin 0` is empty; `Fin 1` is singleton | boundary cases |
| M4 | Arithmetic on `Fin n` (modular) | supporting |
| M5 | `Finset alpha` as `{val : Multiset alpha // val.Nodup}` | core definition |
| M6 | `Finset.empty`, `.singleton`, `.cons`, `.insert` | constructors |
| M7 | `Finset.union`, `.inter`, `.sdiff` | set operations |
| M8 | `Finset.filter`, `.image`, `.map` | transformations |
| M9 | `Finset.card` and cardinality lemmas | counting |
| M10 | `Finset.range n`, `.Icc`, `.Ico` | interval finsets |
| M11 | `Finset.powerset`, `.product` | compound constructions |
| M12 | `Fintype alpha` and `Finset.univ` | type class |
| M13 | `Fintype.card` | type-level counting |
| M14 | `Fintype` instances (products, sums, function types, subtypes) | propagation |
| M15 | `DecidableEq` as prerequisite for `Finset` membership | computability |
| M16 | `List alpha` basic API | sequential type |
| M17 | `List.Nodup`, `List.Perm`, `List.dedup` | list refinements |
| M18 | `Multiset alpha` as `Quot (List.Perm)` | quotient type |
| M19 | `Multiset.card`, `.map`, `.filter`, `.dedup` | multiset operations |
| M20 | List -> Multiset -> Finset pipeline and `toFinset` | hierarchy bridge |
| M21 | `Finsupp alpha M` | finitely supported functions |
| M22 | `Finsupp.single`, `.support`, `.sum` | finsupp API |
| M23 | `Finset.sum` and `Finset.prod` | big operators |
| M24 | Big operator basic API: `sum_empty`, `sum_cons`, `sum_singleton`, `sum_union`, `sum_filter` | API layer |
| M25 | `Finset.sum` over `range`: telescoping, splitting, reindexing | computational patterns |
| M26 | `prod_comm`, `sum_comm` | double sums/products |
| M27 | `Nat.factorial`, `Nat.choose`, `Nat.descFactorial` | combinatorial functions |
| M28 | Pascal's rule: `Nat.choose_succ_succ` | recursion |
| M29 | Binomial theorem | capstone identity |
| M30 | `Nat.choose_symm`, `Nat.choose_zero_right`, `Nat.choose_self` | binomial identities |
| M31 | Vandermonde / sum-of-choose identities | identity family |
| M32 | `Matrix m n alpha` as `m -> n -> alpha` | matrices |
| M33 | `Matrix.of`, `.diagonal`, `.transpose` | matrix constructors |
| M34 | `Matrix.mul` defined via `Finset.sum` | big-op connection |
| M35 | `Set.Finite` vs `Fintype` vs `Finset` distinctions | three notions |
| M36 | `Equiv.Perm (Fin n)` | permutations |
| M37 | `List.permutations` | list enumeration |
| M38 | `Finset.sum_ite`, conditional sums | conditional splitting |
| M39 | Pigeonhole principle | counting argument |
| M40 | Double counting / bijectivity-based cardinality | proof family |

### 3b. Proof-move map (MOVE)

| ID | Move | First needed |
|----|------|-------------|
| V1 | Unfolding a definition to reveal structure (`simp only [...]`, `unfold`, `change`) | World 1 (Fin) |
| V2 | Case splitting / exhaustion on `Fin n` (`fin_cases`, `decide`) | World 2 |
| V3 | Induction on `Nat` with finset-range sums | World 14 |
| V4 | Induction on `Finset` via `Finset.induction_on` | World 10 |
| V5 | Rewriting with membership lemmas (`mem_union`, `mem_filter`, etc.) | World 6 |
| V6 | `ext` to prove finset equality | World 7 |
| V7 | Case analysis on membership (`a in s` or `a not in s`) | World 7 |
| V8 | Choosing a witness from a nonempty finset | World 12 |
| V9 | Contradiction via cardinality | World 12 |
| V10 | Building a finset by explicit construction | World 5 |
| V11 | Splitting a `Finset.sum` at a boundary (`sum_range_succ`) | World 14 |
| V12 | Reindexing a sum | World 16 |
| V13 | Using `simp` with finset lemma families | World 6 |
| V14 | Proving subset relations by intro + membership | World 7 |
| V15 | Cardinality monotonicity from subset | World 10 |
| V16 | Applying the pigeonhole principle | World 12 |
| V17 | Converting between `List.Perm` and `Multiset` equality | World 4 |
| V18 | Using `have` to break a proof into named subgoals | World 1 (review) |
| V19 | Recursive/inductive construction over `Fin n` | World 2 |
| V20 | Algebraic manipulation inside big-operator goals | World 15 |

### 3c. Lean map (LEAN)

| ID | Item | Type | When introduced |
|----|------|------|----------------|
| L1 | `simp` with finset-specific lemmas | tactic | World 6 |
| L2 | `ext` for finset equality | tactic | World 7 |
| L3 | `decide` for decidable propositions | tactic | World 2 |
| L4 | `fin_cases` for exhaustive case analysis | tactic | World 2 |
| L5 | `omega` for natural number arithmetic | tactic | World 1 (baseline, new use) |
| L6 | `norm_num` for numeric computation | tactic | World 2 |
| L7 | `ring` for commutative ring goals | tactic | World 15 |
| L8 | `induction` with `Finset.induction_on` | tactic pattern | World 10 |
| L9 | `rcases` / `obtain` | tactic | NNG4 baseline, deeper use in W6 |
| L10 | `use` for witnesses | tactic | NNG4 baseline |
| L11 | `congr` | tactic | World 15 |
| L12 | `conv` for targeted rewriting under binders | tactic | World 16 |
| L13 | `rfl` | tactic | NNG4 baseline |
| L14 | `calc` for multi-step equational reasoning | tactic | World 14 |
| L15 | `push_cast` / `Nat.cast` | tactic | World 19 |
| L16 | `gcongr` | tactic | World 16 |
| L17 | `refine` | tactic | NNG4 baseline, sophisticated use in W10 |
| L18 | `constructor` | tactic | NNG4 baseline |

**Notation burdens:**
- `{a, b, c}` as `Finset` literal (N1) -- World 5
- `a in s` for membership (N2) -- World 5
- `s cup t`, `s cap t`, `s \ t` (N3) -- World 7
- `s subseteq t` (N4) -- World 7
- `sum x in s, f x` and `prod x in s, f x` (N5) -- World 13
- `Finset.range n` vs `Finset.Icc`/`Ico` (N6) -- World 9
- `|s|` or `s.card` (N7) -- World 9
- Coercion `Fin n -> Nat` (the up-arrow) (N8) -- World 1
- `fun i : Fin n => ...` (N9) -- World 1
- `Finset.univ` (N10) -- World 11
- `::` for `List.cons` vs `Finset.cons` (N11) -- World 3
- `++` for `List.append` (N12) -- World 3
- `Finsupp.single a m` (N13) -- World 21

**Coercion hazards:**
- `Fin n` to `Nat` via `Fin.val` / up-arrow -- must be explicit teaching moment
- `Finset` to `Set` coercion -- hide early, reveal in World 11
- `List` to `Multiset` to `Finset` coercions -- explicit in World 4

### 3d. Misconception map

| ID | Misconception | Where addressed |
|----|--------------|----------------|
| C1 | `Finset` is not `Set` | World 5 (level), World 11 (revisited) |
| C2 | `Finset` requires `DecidableEq` | World 5 (explicit level) |
| C3 | List has order+duplicates; Multiset has duplicates but no order; Finset has neither | World 4 (central lesson) |
| C4 | `Finset.card` counts with multiplicity removed | World 4, World 9 |
| C5 | `Fin 0` is empty, not singleton; `Fin 1` is singleton | World 1 |
| C6 | `Fin n` elements are 0..n-1, not 1..n | World 1 |
| C7 | `insert a s` is a no-op when `a in s` | World 6 |
| C8 | `Finset.sum` requires `AddCommMonoid` | World 13 |
| C9 | `Finset.range n` sums over 0..n-1, not 1..n | World 9 |
| C10 | `Nat.choose n k = 0` when `k > n` | World 18 |
| C11 | `Finsupp` is not a partial function | World 21 |
| C12 | Permutations as `Equiv.Perm` vs lists | World 22 |

---

## 4. World graph

The course is organized into 7 modules (A--G) containing 25 worlds total. Within each module, worlds flow linearly unless otherwise noted. Inter-module dependencies are specified in the graph.

### Module A: Finite index types (`Fin`)

| World | Name | Type | Depends on |
|-------|------|------|-----------|
| W1 | **What is `Fin n`?** | Lecture | (entry point) |
| W2 | **Computing with `Fin`** | Lecture | W1 |
| W3_ex | **The world of `Fin 3`** | Example | W2 |

### Module B: Lists, multisets, and the hierarchy

| World | Name | Type | Depends on |
|-------|------|------|-----------|
| W3 | **Lists: construction and operations** | Lecture | W1 |
| W4 | **Multisets and the hierarchy** | Lecture | W3 |
| W4_ex | **The list `[1,2,1,3]` under three lenses** | Example | W4 |

### Module C: Finsets and their operations

| World | Name | Type | Depends on |
|-------|------|------|-----------|
| W5 | **Constructing finsets** | Lecture | W4 |
| W6 | **Membership, `insert`, and `simp`** | Lecture | W5 |
| W7 | **Union, intersection, difference, and `ext`** | Lecture | W6 |
| W8 | **Filter, image, and map** | Lecture | W7 |
| W8_ex | **Building and inspecting `{1,2,3,4,5}`** | Example | W8 |
| W9 | **Cardinality** | Lecture | W8 |
| W10 | **Finset induction and cardinality proofs** | Lecture | W9 |
| W10_ps | **Finset reasoning** | Pset | W10 |

### Module D: Fintype and counting

| World | Name | Type | Depends on |
|-------|------|------|-----------|
| W11 | **The `Fintype` type class** | Lecture | W10, W2 |
| W12 | **Counting and pigeonhole** | Lecture | W11 |
| W12_ex | **How many functions `Fin 2 -> Fin 3`?** | Example | W12 |
| W12_ps | **Counting and pigeonhole** | Pset | W12 |

### Module E: Big operators

| World | Name | Type | Depends on |
|-------|------|------|-----------|
| W13 | **`Finset.sum`: definition and basic lemmas** | Lecture | W10 |
| W14 | **Induction on range sums** | Lecture | W13 |
| W14_ex | **Sum of the first n natural numbers** | Example | W14 |
| W15 | **`Finset.prod` and algebraic manipulation** | Lecture | W14 |
| W16 | **Splitting, filtering, and reindexing** | Lecture | W15 |
| W16_ps | **Big-operator fluency** | Pset | W16 |

### Module F: Combinatorics and counting identities

| World | Name | Type | Depends on |
|-------|------|------|-----------|
| W17 | **Factorials and descending factorials** | Lecture | W16, W12 |
| W18 | **Binomial coefficients and Pascal's rule** | Lecture | W17 |
| W18_ex | **Pascal's triangle, row by row** | Example | W18 |
| W19 | **Binomial identities and the binomial theorem** | Lecture | W18 |
| W19_ps | **Combinatorial identity transfer** | Pset | W19 |

### Module G: Advanced finite objects (capstone)

| World | Name | Type | Depends on |
|-------|------|------|-----------|
| W20 | **Three notions of finiteness** | Lecture | W11 |
| W21 | **Finitely supported functions** | Lecture | W20, W16 |
| W22 | **Permutations of finite types** | Lecture | W20, W12 |
| W23 | **Matrices as functions over finite types** | Lecture | W22, W16 |
| W24 | **Capstone: integration** | Boss/Review | W23, W21, W19 |

### Dependency diagram (ASCII)

```
W1 (Fin intro)
├── W2 (Fin computing)
│   ├── W3_ex (Fin 3 example)
│   └── W11 (Fintype) ──────────────────────┐
│       ├── W12 (Counting+pigeonhole) ──────┤
│       │   ├── W12_ex (counting functions) │
│       │   ├── W12_ps (pset)               │
│       │   ├── W17 ────────┐               │
│       │   └── W22 ──────┐ │               │
│       └── W20 (3 notions)│ │               │
│           ├── W21 (Finsupp)               │
│           └── W22 (Perms)│ │               │
├── W3 (Lists)             │ │               │
│   └── W4 (Multisets)    │ │               │
│       ├── W4_ex          │ │               │
│       └── W5 (Finset constructors)        │
│           └── W6 (Membership+simp)        │
│               └── W7 (Union/inter/ext)    │
│                   └── W8 (Filter/image)   │
│                       ├── W8_ex           │
│                       └── W9 (Card)       │
│                           └── W10 (Finset induction)
│                               ├── W10_ps  │
│                               ├── W11 ────┘
│                               └── W13 (Finset.sum)
│                                   └── W14 (Range induction)
│                                       ├── W14_ex
│                                       └── W15 (Prod+algebra)
│                                           └── W16 (Split/filter/reindex)
│                                               ├── W16_ps
│                                               ├── W21
│                                               └── W23 (Matrices)
W17 (Factorials) ← W16, W12
└── W18 (Choose + Pascal)
    ├── W18_ex (Pascal's triangle)
    └── W19 (Binomial thm)
        ├── W19_ps
        └── W24 (Capstone) ← W23, W21, W19
```

---

## 5. Level sequences within each world

### W1: What is `Fin n`? (Lecture, ~8 levels)

**World promise**: The learner understands `Fin n` as the subtype `{ i : Nat // i < n }`, can construct elements, extract their values, and handle the boundary cases `Fin 0` and `Fin 1`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Constructing a `Fin`**: Build an element of `Fin 5` using `Fin.mk` | New definition: `Fin n` as subtype; `Fin.mk` constructor | M1 (I), N9 (I) |
| 2 | **Extracting the value**: Given `i : Fin 5`, prove `i.val < 5` | `Fin.val` and the proof obligation; coercion arrow notation | M2 (I), N8 (I) |
| 3 | **`Fin.last` and `Fin.castSucc`**: Construct `Fin.last 4` and prove it equals `(4 : Fin 5)` | Navigation within `Fin` | M2 (S) |
| 4 | **`Fin 0` is empty**: Prove `(h : Fin 0) -> False` | `finZeroElim`; empty types; misconception C5 | M3 (I), C5 (W), V1 (I) |
| 5 | **`Fin 1` is a singleton**: Prove all elements of `Fin 1` are equal | Uniqueness in `Fin 1`; subtype equality | M3 (S), C5 (S) |
| 6 | **Coercion in action**: Prove a statement about `(i : Fin n)` after coercing to `Nat` | The up-arrow coercion; `omega` for the arithmetic | N8 (S), L5 (S), C6 (W) |
| 7 | **`Fin.succ` and successor navigation**: Show `Fin.succ i` has value `i.val + 1` | Successor function on `Fin` | M2 (S) |
| 8 | **Boss: A property of all elements of `Fin 4`** : Prove a universally quantified statement about `Fin 4` by combining `Fin.val`, coercion, and `omega` | Integration of M1--M3, V1, N8 | M1--M3 (G), V18 (R) |

**Transfer moment (conclusion of boss)**: Restate the proof in plain English -- "We need to show something holds for every element of a 4-element set. Each element is a natural number less than 4, so there are exactly four cases: 0, 1, 2, 3."

### W2: Computing with `Fin` (Lecture, ~8 levels)

**World promise**: The learner can do exhaustive case analysis on small `Fin n` using `fin_cases` and `decide`, and understands modular arithmetic on `Fin n`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Introducing `fin_cases`**: Prove a proposition about all elements of `Fin 3` using `fin_cases` | New tactic: `fin_cases` | L4 (I), V2 (I) |
| 2 | **`fin_cases` with `omega` cleanup**: A `Fin 4` proposition where each case needs `omega` | Combining `fin_cases` + `omega` | L4 (S), L5 (S) |
| 3 | **Introducing `decide`**: Prove a decidable proposition on `Fin 3` with `decide` | New tactic: `decide` | L3 (I) |
| 4 | **When to use `decide` vs `fin_cases`**: Two similar goals, one solved by `decide`, the other needing `fin_cases` + reasoning | Tactic selection | L3 (S), L4 (S) |
| 5 | **Introducing `norm_num`**: Evaluate a numeric expression involving `Fin.val` | New tactic: `norm_num` | L6 (I) |
| 6 | **Arithmetic on `Fin n`**: Addition and subtraction modulo n | Modular arithmetic; M4 | M4 (I) |
| 7 | **Building a function on `Fin n`**: Define a function `Fin 3 -> Nat` by cases | Recursive/inductive construction; V19 | V19 (I), N9 (S) |
| 8 | **Boss: A nontrivial property of `Fin 5`**: Prove that a specific function on `Fin 5` satisfies a property, requiring `fin_cases` + `norm_num` + `omega` | Integration of L3--L6, V2, M4 | L4 (G), L6 (G), V2 (G) |

### W3_ex: The world of `Fin 3` (Example, ~6 levels)

**World promise**: The learner has concretized `Fin` by exhaustively working with `Fin 3` as the set `{0, 1, 2}`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Enumerating all elements**: Prove `Fin 3` has exactly 3 elements by exhaustion | Concretization of `Fin` | E1 (I) |
| 2 | **A function on `Fin 3`**: Define and compute with a specific function `Fin 3 -> Nat` | Functions on concrete finite types | E1 (S), N9 (R) |
| 3 | **Pairing elements**: Build an element of `Fin 3 x Fin 3` | Product types over `Fin` | M14 (preview) |
| 4 | **Injectivity on `Fin 3`**: Prove a specific function `Fin 3 -> Fin 4` is injective | Injectivity as a proof move on concrete types | V2 (R) |
| 5 | **Surjectivity fails**: Show a specific function `Fin 3 -> Fin 4` cannot be surjective | Counterexample thinking; pigeonhole preview | V9 (preview) |
| 6 | **Transfer**: State in words what `Fin 3` represents and why `Fin 0` is empty | T1 (I), T8 (I) |

### W3: Lists: construction and operations (Lecture, ~8 levels)

**World promise**: The learner can construct lists, reason about membership, and use basic list operations (`cons`, `append`, `length`, `map`, `filter`).

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **The empty list and `cons`**: Construct `[1, 2, 3]` from `[]` and `::` | List constructors | M16 (I), N11 (I) |
| 2 | **List membership**: Prove `2 in [1, 2, 3]` | `List.mem` and `simp` | M16 (S) |
| 3 | **`List.length`**: Prove `[1, 2, 3].length = 3` | Length computation | M16 (S) |
| 4 | **`List.append`**: Prove a property of `[1, 2] ++ [3, 4]` | Append and notation `++` | M16 (S), N12 (I) |
| 5 | **`List.map`**: Apply a function to a list and prove a membership result | `List.map` | M16 (S) |
| 6 | **`List.filter`**: Filter a list by a predicate | `List.filter` | M16 (S) |
| 7 | **`List.Nodup`**: Prove a specific list has no duplicates, and show one that does | `Nodup` property; setup for multisets | M17 (I) |
| 8 | **Boss: A list manipulation proof**: Combine `map`, `filter`, `length`, and membership in one proof | Integration | M16 (G) |

### W4: Multisets and the hierarchy (Lecture, ~9 levels)

**World promise**: The learner understands `Multiset` as the quotient of lists by permutation, and the full `List -> Multiset -> Finset` pipeline.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **What is a `Multiset`?**: Convert a list to a multiset | `Multiset` definition as quotient | M18 (I) |
| 2 | **`List.Perm` and multiset equality**: Two lists that are permutations give the same multiset | Permutation equivalence | M17 (S), V17 (I) |
| 3 | **Multiset operations**: `Multiset.card`, `Multiset.map` on a concrete example | Multiset API | M19 (I) |
| 4 | **Multiset has duplicates**: Show a multiset can have repeated elements | Contrast with finsets | C3 (I) |
| 5 | **`toFinset` removes duplicates**: Convert a multiset with duplicates to a finset | The pipeline | M20 (I) |
| 6 | **Information loss**: Show that two different lists can produce the same finset | Why `toFinset` loses information; C3 reinforced | C3 (S), E15 (I) |
| 7 | **The three-layer hierarchy**: Given a list, compute its multiset and finset, compare cardinalities | Central lesson of the world | M20 (S), C3 (G), C4 (I) |
| 8 | **`Multiset.dedup` and `Multiset.toFinset`**: Show the relationship | Deduplication | M19 (S), M20 (S) |
| 9 | **Boss: A hierarchy proof**: Given `[1, 2, 1, 3, 2]`, trace it through all three layers and prove cardinality results | Integration of M16--M20, C3, C4 | M20 (G), C3 (G) |

**Transfer moment**: "In ordinary math, we often say 'the set of elements in the list.' In Lean, that's `toFinset`, and it drops duplicates and forgets order."

### W4_ex: The list `[1,2,1,3]` under three lenses (Example, ~5 levels)

**World promise**: The learner sees the same concrete data processed as a list, a multiset, and a finset, cementing the hierarchy distinctions.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **As a `List`**: Compute length, check membership, verify `2 in [1,2,1,3]` | List perspective | E15 (S) |
| 2 | **As a `Multiset`**: Convert, show card = 4 (duplicates kept) | Multiset perspective | C3 (R) |
| 3 | **As a `Finset`**: Convert, show card = 3 (duplicate removed) | Finset perspective | C4 (S), E15 (S) |
| 4 | **Reordering doesn't change the multiset**: Prove `[1,2,1,3]` and `[3,1,2,1]` give the same multiset | Permutation invariance | V17 (R) |
| 5 | **Transfer**: State in plain English why `|{1,2,3}| = 3` even though the list has 4 elements | T9 (I) |

### W5: Constructing finsets (Lecture, ~8 levels)

**World promise**: The learner can construct finsets using `empty`, `singleton`, `cons`, `insert`, and the `{a, b, c}` notation, and understands `DecidableEq`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **The empty finset**: Prove `(Finset.empty : Finset Nat) = {}` | `Finset.empty` | M6 (I), E10 (I) |
| 2 | **Singletons**: Construct `{5}` as `Finset.singleton 5` | `Finset.singleton` | M6 (S) |
| 3 | **`insert`**: Build `{1, 2}` from `insert 1 {2}` | `Finset.insert` | M6 (S), N1 (I) |
| 4 | **The `{a, b, c}` notation**: Prove `{1, 2, 3} = insert 1 (insert 2 {3})` | Notation desugaring | N1 (S) |
| 5 | **`Finset.cons` and the proof obligation**: Use `cons` when you have a proof of non-membership | `Finset.cons` vs `insert` | M6 (S) |
| 6 | **Why `DecidableEq` matters**: Encounter a type-class error and understand why finset membership needs decidable equality | C2 misconception | M15 (I), C2 (W) |
| 7 | **`Finset` vs `Set`**: Attempt to apply a `Set` lemma to a `Finset` and see why it fails | C1 misconception | C1 (W), M35 (preview) |
| 8 | **Boss: Build a specific finset three ways**: Construct the same finset using `insert`, `cons`, and literal notation; prove all three are equal | Integration of M6, N1 | M6 (G), N1 (G) |

### W6: Membership, `insert`, and `simp` (Lecture, ~9 levels)

**World promise**: The learner can prove membership goals using `simp` with finset lemmas, and understands that `insert` is idempotent.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Membership in a literal finset**: Prove `2 in ({1, 2, 3} : Finset Nat)` | `Finset.mem` and `simp` | N2 (I), V5 (I) |
| 2 | **`mem_insert`**: Prove membership after an insert | Rewriting with `mem_insert` | V5 (S) |
| 3 | **`mem_singleton`**: Simplify membership in `{a}` | Membership lemma family | V5 (S) |
| 4 | **Introducing `simp` with finset lemmas**: Use `simp [Finset.mem_insert, Finset.mem_singleton]` | New tactic: `simp` with lemma list | L1 (I), V13 (I) |
| 5 | **`simp` vs manual rewriting**: Solve the same goal both ways | When `simp` is appropriate vs manual control | L1 (S) |
| 6 | **`insert` is idempotent**: Prove `insert 2 {1, 2, 3} = {1, 2, 3}` | C7 misconception | C7 (W) |
| 7 | **Non-membership**: Prove `4 not in ({1, 2, 3} : Finset Nat)` | Negation of membership | V5 (S) |
| 8 | **Destructuring membership**: Given `x in insert a s`, case-split into `x = a` or `x in s` | `rcases` on membership | L9 (S) |
| 9 | **Boss: A membership reasoning chain**: Multi-step membership proof combining `insert`, `simp`, and case splitting | Integration of V5, V13, L1 | L1 (G), V5 (G) |

### W7: Union, intersection, difference, and `ext` (Lecture, ~10 levels)

**World promise**: The learner can prove goals involving finset union, intersection, and symmetric difference, and can prove finset equality via `ext`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Finset.union`**: Prove `x in s cup t iff x in s or x in t` | Union membership lemma | M7 (I), N3 (I) |
| 2 | **`Finset.inter`**: Prove `x in s cap t iff x in s and x in t` | Intersection membership | M7 (S), N3 (S) |
| 3 | **`Finset.sdiff`**: Prove `x in s \ t iff x in s and x not in t` | Set difference | M7 (S), N3 (S) |
| 4 | **Combining operations**: Prove a membership in `(s cup t) cap u` | Multi-step membership reasoning | V5 (R) |
| 5 | **Introducing `ext`**: Prove `s cup t = t cup s` via extensionality | New tactic: `ext` | L2 (I), V6 (I) |
| 6 | **`ext` for intersection**: Prove `s cap t = t cap s` | `ext` practice | L2 (S), V6 (S) |
| 7 | **Subset via `intro`**: Prove `s subseteq s cup t` by introducing an element | Subset proof pattern | V14 (I), N4 (I) |
| 8 | **Case analysis on membership**: Use `by_cases h : a in s` to split | `Decidable.em` for membership | V7 (I) |
| 9 | **Distributivity**: Prove `s cap (t cup u) = (s cap t) cup (s cap u)` | Complex `ext` proof with case analysis | V6 (R), V7 (S) |
| 10 | **Boss: A set-algebraic identity**: Prove `s \ (t cap u) = (s \ t) cup (s \ u)` | Integration of M7, V5, V6, V7, V14 | M7 (G), V6 (G) |

**Transfer moment**: "This is De Morgan's law for finite sets. In ordinary math, you'd prove it by taking an arbitrary element and chasing membership. That's exactly what `ext` + `simp` does."

### W8: Filter, image, and map (Lecture, ~8 levels)

**World promise**: The learner can filter finsets by predicates, map functions over finsets, and reason about membership in the resulting finsets.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Finset.filter`**: Filter `{1,2,3,4,5}` by a predicate | `Finset.filter` and `mem_filter` | M8 (I) |
| 2 | **`mem_filter` rewriting**: Prove membership in a filtered finset | Rewriting with `mem_filter` | V5 (R) |
| 3 | **`Finset.image`**: Map a function over a finset | `Finset.image` and `mem_image` | M8 (S) |
| 4 | **`mem_image` and witnesses**: Prove `y in Finset.image f s` by providing a witness | `use` for image membership | M8 (S), L10 (R) |
| 5 | **`Finset.map` vs `Finset.image`**: Understand that `map` requires an embedding (injective function) | `map` vs `image` distinction | M8 (S) |
| 6 | **Composing filter and image**: Filter then map, or map then filter | Compositionality | M8 (R) |
| 7 | **Image can shrink cardinality**: Show that `image` of a non-injective function has fewer elements | Non-injective image | C4 (R) |
| 8 | **Boss: Filter-image reasoning**: Given a finset, filter, map, and prove a membership/cardinality result | Integration of M8 | M8 (G) |

### W8_ex: Building and inspecting `{1,2,3,4,5}` (Example, ~7 levels)

**World promise**: The learner works concretely with a single finset, applying all finset operations learned so far.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Build it three ways**: Construct `{1,2,3,4,5}` using literal notation, iterated insert, and `Finset.range 5` with image | Concretization | E3 (I), E2 (I) |
| 2 | **Membership checks**: Verify `3 in {1,2,3,4,5}` and `6 not in {1,2,3,4,5}` | Retrieval of membership | V5 (R), V13 (R) |
| 3 | **Filter the evens**: Compute `Finset.filter (fun x => x % 2 = 0) {1,2,3,4,5}` | Concrete filter | M8 (R) |
| 4 | **Image under squaring**: Compute `Finset.image (fun x => x^2) {1,2,3,4,5}` | Concrete image | M8 (R) |
| 5 | **Power set**: Show `{1,2,3}.powerset` has 8 elements | Concretization of powerset | M11 (preview), E8 (I) |
| 6 | **Product**: Compute `{1,2} x {3,4}` as a finset of pairs | Concretization of product | M11 (preview), E19 (I) |
| 7 | **Transfer**: Describe in words what `filter`, `image`, and `powerset` do to a finite set | T8 (S), T1 (S) |

### W9: Cardinality (Lecture, ~9 levels)

**World promise**: The learner can compute and reason about `Finset.card`, including the key cardinality lemmas.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`card_empty`**: Prove `(Finset.empty : Finset Nat).card = 0` | Base cardinality | M9 (I), N7 (I) |
| 2 | **`card_singleton`**: Prove `{a}.card = 1` | Singleton cardinality | M9 (S) |
| 3 | **`card_insert_of_not_mem`**: Prove that inserting a new element increases card by 1 | The key insertion lemma; requires non-membership hypothesis | M9 (S) |
| 4 | **`card_insert` when element is already present**: Show card doesn't change | C7 revisited via cardinality | C7 (R), M9 (S) |
| 5 | **`Finset.range` and its cardinality**: Prove `(Finset.range n).card = n` | Interval finsets | M10 (I), N6 (I) |
| 6 | **`Finset.range 0` is empty**: Misconception calibration | C9 boundary | C9 (W), E16 (I) |
| 7 | **Inclusion-exclusion**: Prove `card (s cup t) + card (s cap t) = card s + card t` | The central cardinality identity | M9 (S), T4 (I) |
| 8 | **Cardinality of filter**: Prove `card (filter p s) <= card s` | Filter bound | M9 (S) |
| 9 | **Boss: A cardinality computation**: Given two specific finsets, compute the cardinality of their union and intersection | Integration of M9, M10, T4 | M9 (G), T4 (S) |

**Transfer moment**: "In ordinary math, inclusion-exclusion says |A union B| = |A| + |B| - |A inter B|. The Lean version is the additive form. Both express the same principle: elements in the overlap get counted twice."

### W10: Finset induction and cardinality proofs (Lecture, ~9 levels)

**World promise**: The learner can use `Finset.induction_on` as an induction principle distinct from `Nat.induction`, and can prove cardinality results by induction on finsets.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Recalling `Nat` induction**: A simple `Nat.rec` proof as baseline | Review of NNG4 induction | V3 (review) |
| 2 | **Introducing `Finset.induction_on`**: The base case (empty finset) and the inductive step (insert an element not already present) | New induction principle | V4 (I), L8 (I) |
| 3 | **First `Finset.induction_on` proof**: Prove a simple property of all finsets | Practicing the new induction pattern | V4 (S), L8 (S) |
| 4 | **The inductive step in detail**: Why the hypothesis `a not in s` matters | Understanding the non-membership assumption | V4 (S) |
| 5 | **A cardinality-by-induction proof**: Prove a cardinality result using `Finset.induction_on` | Combining V4 with M9 | V4 (S), M9 (R) |
| 6 | **Subset implies cardinality inequality**: Prove `s subseteq t -> card s <= card t` | V15 as a proof move | V15 (I) |
| 7 | **Comparing `Nat.induction` and `Finset.induction_on`**: The same theorem proved both ways | Explicit comparison | V3 (R), V4 (R) |
| 8 | **Using `refine` to partially fill induction goals**: Use `refine Finset.induction_on s ?_ ?_` | Sophisticated `refine` usage | L17 (S) |
| 9 | **Boss: A non-trivial finset induction**: Prove a property of all finsets that requires careful management of the inductive hypothesis | Integration of V4, L8, V15 | V4 (G), L8 (G) |

### W10_ps: Finset reasoning (Pset, ~8 levels)

**World promise**: The learner retrieves finset skills (membership, set operations, cardinality, induction) under reduced scaffolding on fresh surface forms.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Fresh membership goal**: A membership proof in a new context | Retrieval of V5 | V5 (T) |
| 2 | **Subset from a condition**: Prove subset given a property | Retrieval of V14 | V14 (T) |
| 3 | **Set-operation identity (fresh)**: A new De Morgan-style identity | Retrieval of V6, V7 | V6 (T), V7 (T) |
| 4 | **Filter and card**: Compute the cardinality of a filtered finset | Retrieval of M8, M9 | M8 (T), M9 (T) |
| 5 | **Induction on a new property**: Use `Finset.induction_on` on a fresh target | Retrieval of V4 | V4 (T) |
| 6 | **Transfer: State inclusion-exclusion in words**: Given a Lean statement, write the paper-proof version | T4 (R) |
| 7 | **Transfer: Subset argument in words**: Translate a subset-cardinality argument to paper | T3 (I) |
| 8 | **Boss: Multi-step finset reasoning**: A proof combining 4+ moves from Modules B--C | Integration | V5 (G), V6 (G), V14 (G), M9 (G) |

### W11: The `Fintype` type class (Lecture, ~8 levels)

**World promise**: The learner understands `Fintype` as the type class that equips a type with a universal finset, and can use `Finset.univ` and `Fintype.card`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **What is `Fintype`?**: Show that `Fin n` is a `Fintype` by accessing `Finset.univ` | `Fintype` definition | M12 (I), N10 (I) |
| 2 | **`Finset.univ` contains all elements**: Prove `x in (Finset.univ : Finset (Fin 3))` for any `x` | The universal finset | M12 (S) |
| 3 | **`Fintype.card` equals `Finset.univ.card`**: Prove the relationship | The counting bridge | M13 (I) |
| 4 | **`Fintype.card (Fin n) = n`**: The fundamental count | Concrete cardinality | M13 (S) |
| 5 | **`Bool` as a `Fintype`**: Prove `Fintype.card Bool = 2` | `Fintype` instance for `Bool` | M14 (I), E13 (I) |
| 6 | **Product types**: Prove `Fintype.card (Fin 2 x Fin 3) = 6` | `Fintype` propagation to products | M14 (S) |
| 7 | **`Nat` is NOT a `Fintype`**: Show that `Nat` has no `Fintype` instance (explain the error) | Counterexample | E14 (I), M35 (I) |
| 8 | **Boss: Cardinality of `Fin 2 x Bool`**: Compute `Fintype.card` for a compound type | Integration of M12--M14 | M12 (G), M13 (G), M14 (G) |

### W12: Counting and pigeonhole (Lecture, ~10 levels)

**World promise**: The learner can count elements of compound finite types and apply the pigeonhole principle.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Cardinality of sum types**: Prove `Fintype.card (Fin 2 + Fin 3) = 5` | `Fintype.card_sum` | M14 (S) |
| 2 | **Cardinality of function types**: Prove `Fintype.card (Fin 2 -> Fin 3) = 9` | `Fintype.card_fun` | M14 (S), E9 (I) |
| 3 | **Cardinality of subtypes**: Count elements of `{ x : Fin 5 // x.val % 2 = 0 }` | `Fintype` for subtypes | M14 (S) |
| 4 | **Choosing a witness from a nonempty finset**: Given `s.Nonempty`, extract an element | V8 proof move | V8 (I) |
| 5 | **Contradiction via cardinality**: If `card s = 0`, then `s` is empty | V9 proof move | V9 (I) |
| 6 | **Stating the pigeonhole principle**: If `f : Fin (n+1) -> Fin n`, then `f` is not injective | The theorem statement | M39 (I) |
| 7 | **Proving pigeonhole (guided)**: Walk through the proof of pigeonhole using cardinality | V16 proof move | V16 (I), M39 (S) |
| 8 | **Applying pigeonhole**: Use pigeonhole to prove a specific non-injectivity result | Applying the principle | V16 (S), T5 (I) |
| 9 | **A concrete pigeonhole application**: "If 6 people are in 5 rooms, two share a room" | V16 on natural language | V16 (S), T5 (S) |
| 10 | **Boss: A counting argument**: Combine `Fintype.card` with pigeonhole on a compound type | Integration of M14, M39, V16 | M39 (G), V16 (G) |

**Transfer moment**: "In paper math, the pigeonhole principle says: if you put n+1 objects into n boxes, some box has at least two objects. The Lean version says the corresponding function cannot be injective."

### W12_ex: How many functions `Fin 2 -> Fin 3`? (Example, ~5 levels)

**World promise**: The learner concretely enumerates functions between small finite types and connects this to the multiplication principle.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Enumerating the functions**: List all 9 functions from `Fin 2` to `Fin 3` conceptually; verify `Fintype.card = 9` | Concretization | E9 (S) |
| 2 | **Which are injective?**: Count the injective functions among them | Counting with constraints | M40 (preview) |
| 3 | **Which are surjective?**: Argue why no function `Fin 2 -> Fin 3` can be surjective | Pigeonhole in reverse | V16 (R) |
| 4 | **`Fin 3 -> Bool` has 8 elements**: Compute and connect to `2^3` | Exponential counting | E9 (S) |
| 5 | **Transfer: The multiplication principle**: State why `|Fin 2 -> Fin 3| = 3^2` in ordinary language | T1 (R) |

### W12_ps: Counting and pigeonhole (Pset, ~7 levels)

**World promise**: The learner retrieves counting and pigeonhole skills under reduced scaffolding.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Count a new compound type**: Compute `Fintype.card` for a type not seen before | Retrieval of M13, M14 | M13 (T), M14 (T) |
| 2 | **A fresh pigeonhole application**: Apply pigeonhole in a new setting | Retrieval of V16 | V16 (T) |
| 3 | **Cardinality comparison**: Use subset + cardinality to derive an inequality | Retrieval of V15 | V15 (T) |
| 4 | **A nonemptiness argument**: From cardinality > 0, extract a witness | Retrieval of V8, V9 | V8 (T), V9 (T) |
| 5 | **Transfer: Pigeonhole in words**: Given a Lean proof, restate it as a paper proof | T5 (R) |
| 6 | **Transfer: Counting in words**: Explain why `Fin m -> Fin n` has `n^m` elements | T1 (T) |
| 7 | **Boss: Multi-step counting argument**: A proof combining counting, pigeonhole, and subset reasoning | Integration | M39 (G), V15 (G), V16 (G) |

### W13: `Finset.sum`: definition and basic lemmas (Lecture, ~9 levels)

**World promise**: The learner can write and simplify big-sum expressions, and knows the basic API (`sum_empty`, `sum_singleton`, `sum_cons`, `sum_union`).

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **What is `Finset.sum`?**: Explain the `sum x in s, f x` notation; compute a simple sum | Big operator concept + notation | M23 (I), N5 (I) |
| 2 | **`sum_empty`**: Prove `sum x in empty, f x = 0` | Base case | M24 (I) |
| 3 | **`sum_singleton`**: Prove `sum x in {a}, f x = f a` | Singleton sum | M24 (S) |
| 4 | **`sum_cons`**: Prove `sum x in cons a s h, f x = f a + sum x in s, f x` | The cons decomposition | M24 (S) |
| 5 | **`sum_insert`**: The analogous lemma for `insert` (with non-membership) | Insert decomposition | M24 (S) |
| 6 | **The `AddCommMonoid` requirement**: Why `Finset.sum` needs commutativity | Type class requirement; C8 misconception | C8 (W) |
| 7 | **Computing a concrete sum**: Evaluate `sum x in {1,2,3}, x^2` step by step | Concrete computation | M23 (S) |
| 8 | **`sum_union` for disjoint sets**: Prove the additive splitting | Union splitting | M24 (S) |
| 9 | **Boss: Simplify a big-sum expression**: Multi-step simplification combining cons, singleton, and union decompositions | Integration of M23, M24 | M23 (G), M24 (G) |

### W14: Induction on range sums (Lecture, ~9 levels)

**World promise**: The learner can prove equalities about `sum i in range n, f i` by induction, peeling off the last term with `sum_range_succ`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Finset.range` recap**: Verify `range 4 = {0,1,2,3}` and its cardinality | Range review | M10 (R), C9 (R) |
| 2 | **`sum_range_succ`**: Prove `sum i in range (n+1), f i = sum i in range n, f i + f n` | The peeling-off lemma | M25 (I), V11 (I) |
| 3 | **First inductive sum proof**: Prove `sum i in range n, 1 = n` by induction | Induction + `sum_range_succ` | V3 (I), V11 (S) |
| 4 | **Setting up a `calc` proof**: Use `calc` to chain equalities in an inductive step | New tactic pattern: `calc` | L14 (I) |
| 5 | **A slightly harder sum**: Prove `sum i in range n, 2 = 2 * n` | Practice with `omega`/`ring` in inductive step | V3 (S) |
| 6 | **Sum of `i` from 0 to n-1**: Prove `sum i in range n, i = n * (n-1) / 2` (for natural numbers, adjusted) | The classic sum formula | E4 (preview), V3 (S) |
| 7 | **The inductive step in detail**: Walk through a moderately complex inductive step | Coaching for boss | V3 (S), V11 (R) |
| 8 | **Base case pitfalls**: Show that `range 0 = empty` means the base case is trivial | C9 revisited, base case skill | C9 (R) |
| 9 | **Boss: Prove a sum identity by induction**: A non-trivial identity requiring `sum_range_succ` + induction + `omega` | Integration of V3, V11, L14, M25 | V3 (G), M25 (G) |

**Transfer moment**: "In ordinary math, you'd write: 'We prove by induction on n. Base case: when n = 0, the sum is empty and equals 0. Inductive step: assuming the formula for n, the sum up to n+1 adds the (n+1)-th term...' This is exactly what `sum_range_succ` + `induction` does in Lean."

### W14_ex: Sum of the first n natural numbers (Example, ~6 levels)

**World promise**: The learner proves the classic formula sum_{i=0}^{n-1} i = n(n-1)/2 in full, and sees the connection to ordinary sigma notation.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Compute the sum for small n**: Verify the formula for n = 0, 1, 2, 3, 4 using `decide` or `norm_num` | Concrete verification | E4 (I) |
| 2 | **State the theorem**: Write the formal statement | Statement writing | E4 (S) |
| 3 | **Prove the base case**: Induction base for the sum formula | Base case practice | V3 (R) |
| 4 | **Prove the inductive step**: The algebraic core of the proof | Inductive step practice | V3 (R), V11 (R) |
| 5 | **The full proof**: Combine into a complete inductive proof | Full proof assembly | E4 (S), V3 (G) |
| 6 | **Transfer: Write the proof on paper**: Restate the Lean proof as a standard mathematical induction proof | T2 (I), T10 (I) |

### W15: `Finset.prod` and algebraic manipulation (Lecture, ~8 levels)

**World promise**: The learner understands `Finset.prod`, can work with both additive and multiplicative big operators, and can do algebraic manipulation inside big-operator goals.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Finset.prod`: definition**: Introduce `prod x in s, f x` | `Finset.prod` | M23 (S) |
| 2 | **`prod_empty` and `prod_singleton`**: Base cases for products | Product API | M24 (R) |
| 3 | **`prod_range_succ`**: Peel off the last factor | Multiplicative peeling | M25 (S) |
| 4 | **Introducing `ring`**: Use `ring` to close algebraic subgoals inside big-operator proofs | New tactic: `ring` | L7 (I) |
| 5 | **`sum_add_sum` / distributing operations**: Prove `sum (f + g) = sum f + sum g` | Algebraic manipulation inside sums; V20 | V20 (I) |
| 6 | **`sum_mul` / pulling a constant out**: Prove `sum (c * f) = c * sum f` | Constant factor extraction | V20 (S) |
| 7 | **`congr` for big operators**: Change the function inside a sum/product | `congr` tactic | L11 (I) |
| 8 | **Boss: Algebraic big-operator identity**: Prove an identity that requires both `sum` and `prod` manipulations | Integration of M23, V20, L7, L11 | V20 (G), L7 (G) |

### W16: Splitting, filtering, and reindexing (Lecture, ~9 levels)

**World promise**: The learner can split sums by predicate, filter sums, and reindex using `sum_bij` or `sum_equiv`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`sum_filter`**: Split a sum by filtering | Filter decomposition | M38 (I) |
| 2 | **`sum_ite`**: Split a sum by a conditional | Conditional splitting | M38 (S) |
| 3 | **Splitting a sum into two parts**: Decompose `range (m + n)` into two ranges | Sum splitting | M25 (S) |
| 4 | **`sum_comm` for double sums**: Interchange summation order | Double sums | M26 (I) |
| 5 | **Introducing `conv`**: Rewrite inside a binder using `conv` | New tactic: `conv` | L12 (I) |
| 6 | **Introducing `gcongr`**: Use `gcongr` for monotone inequality goals on sums | New tactic: `gcongr` | L16 (I) |
| 7 | **Basic reindexing**: Reindex `sum i in range n, f i` to `sum i in range n, f (n - 1 - i)` | V12 proof move | V12 (I) |
| 8 | **A reindexing proof**: Use `sum_bij` or `sum_equiv` for a concrete reindexing | V12 practice | V12 (S) |
| 9 | **Boss: A splitting + reindexing proof**: Combine filtering, splitting, and reindexing in one proof | Integration of M25, M26, M38, V12 | M25 (G), V12 (G) |

### W16_ps: Big-operator fluency (Pset, ~8 levels)

**World promise**: The learner retrieves big-operator skills on fresh surface forms with reduced scaffolding.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Fresh inductive sum**: A new identity proved by induction | Retrieval of V3, V11 | V3 (T), V11 (T) |
| 2 | **Product by induction**: A product identity proved by induction | Retrieval of M25 (multiplicative) | M25 (T) |
| 3 | **Algebraic manipulation in a sum**: Simplify a sum using `ring` and `congr` | Retrieval of V20, L7 | V20 (T), L7 (T) |
| 4 | **Filtering a sum**: Use `sum_filter` on a new predicate | Retrieval of M38 | M38 (T) |
| 5 | **Double sum**: Interchange summation order in a new setting | Retrieval of M26 | M26 (T) |
| 6 | **Transfer: Read sigma notation**: Given a Lean `sum` expression, write it as standard math notation | T10 (S) |
| 7 | **Transfer: Write an inductive sum proof on paper**: Translate a Lean proof to paper | T2 (R) |
| 8 | **Boss: Multi-step big-operator proof**: Requires induction + algebraic manipulation + possibly reindexing or filtering | Integration | V3 (G), V20 (G), M25 (G) |

### W17: Factorials and descending factorials (Lecture, ~7 levels)

**World promise**: The learner understands `Nat.factorial`, `Nat.descFactorial`, and can compute with them.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Nat.factorial` definition**: Compute `5! = 120` | Factorial definition | M27 (I), E7 (I) |
| 2 | **Factorial recursion**: Prove `(n+1)! = (n+1) * n!` | Recursive structure | M27 (S) |
| 3 | **Factorial and `Finset.prod`**: Express `n!` as `prod i in range n, (i+1)` | Connecting factorial to big operators | M27 (S), M23 (R) |
| 4 | **`Nat.descFactorial`**: Compute `descFactorial 5 3` | Descending factorial | M27 (S) |
| 5 | **Relationship between factorial and descFactorial**: Prove the key identity | Algebraic identity | M27 (S) |
| 6 | **Factorial and counting permutations**: The number of permutations of `n` elements is `n!` | Preview of permutations | M36 (preview) |
| 7 | **Boss: A factorial identity**: Prove an identity involving factorials by induction | Integration of M27 | M27 (G) |

### W18: Binomial coefficients and Pascal's rule (Lecture, ~9 levels)

**World promise**: The learner understands `Nat.choose`, can compute specific values, and can prove Pascal's rule and basic identities.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Nat.choose` definition**: Compute `Nat.choose 5 2 = 10` | Binomial coefficient definition | M27 (S), E6 (I) |
| 2 | **Boundary values**: Prove `choose n 0 = 1`, `choose n n = 1`, `choose 0 (k+1) = 0` | Boundary identities | M30 (I) |
| 3 | **`choose n k = 0` when `k > n`**: Verify for specific values | C10 misconception | C10 (W) |
| 4 | **Pascal's rule**: State and prove `choose (n+1) (k+1) = choose n k + choose n (k+1)` | The central recursion | M28 (I) |
| 5 | **Pascal's rule in action**: Use Pascal's rule to compute `choose 5 2` from smaller values | Concrete application | M28 (S), E17 (I) |
| 6 | **Symmetry**: Prove `choose n k = choose n (n-k)` | `Nat.choose_symm` | M30 (S) |
| 7 | **`choose` as counting subsets**: Explain that `choose n k` counts k-element subsets of an n-element set | Combinatorial interpretation | T7 (I) |
| 8 | **Row sum**: Prove `sum k in range (n+1), choose n k = 2^n` | Sum identity | M31 (I) |
| 9 | **Boss: A binomial coefficient identity**: Prove a non-trivial identity using Pascal's rule and induction | Integration of M27, M28, M30 | M28 (G), M30 (G) |

### W18_ex: Pascal's triangle, row by row (Example, ~6 levels)

**World promise**: The learner computes explicit rows of Pascal's triangle and sees the pattern before the general theory.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Row 0**: `[1]` | Trivial row | E17 (S) |
| 2 | **Row 1**: `[1, 1]` -- verify using Pascal's rule | Recursion in action | E17 (S), M28 (R) |
| 3 | **Row 2**: `[1, 2, 1]` | Pattern emergence | E17 (S) |
| 4 | **Row 4**: `[1, 4, 6, 4, 1]` -- verify the row sum equals 16 | Row sum + computation | E17 (S), M31 (S) |
| 5 | **Symmetry visible**: Check that row 4 is symmetric | `choose_symm` concretized | M30 (R) |
| 6 | **Transfer**: Draw Pascal's triangle and explain the recursion in words | T7 (S) |

### W19: Binomial identities and the binomial theorem (Lecture, ~10 levels)

**World promise**: The learner can prove the binomial theorem and several binomial-coefficient identities, and can work with `push_cast`/`Nat.cast` when sums land in other types.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Preparing for the binomial theorem**: Express `(a + b)^n` as a sum | Setting up the statement | M29 (preview) |
| 2 | **Introducing `push_cast`**: When a sum of natural numbers lands in `Int` or another type | New tactic: `push_cast` | L15 (I) |
| 3 | **The binomial theorem (base case)**: Prove for `n = 0` | Induction base | M29 (I) |
| 4 | **The binomial theorem (inductive step, part 1)**: Set up the inductive step; expand `(a + b) * (a + b)^n` | First half of the inductive step | M29 (S) |
| 5 | **The binomial theorem (inductive step, part 2)**: Use Pascal's rule to recombine terms | Second half; Pascal's rule as ingredient | M29 (S), M28 (R) |
| 6 | **The binomial theorem (assembly)**: Combine into the full proof | Full theorem | M29 (S) |
| 7 | **Vandermonde convolution**: State and prove `sum k, choose m k * choose n (p-k) = choose (m+n) p` | Advanced identity | M31 (S) |
| 8 | **Alternating sum of binomial coefficients**: Prove `sum k, (-1)^k * choose n k = 0` for `n >= 1` | Sign manipulation in sums | M31 (S) |
| 9 | **Transfer: State the binomial theorem in ordinary notation**: Write `(a+b)^n = sum_{k=0}^{n} choose(n,k) a^k b^{n-k}` | T7 (R), T10 (R) |
| 10 | **Boss: A combined binomial identity**: Prove an identity that requires the binomial theorem plus algebraic manipulation | Integration of M28, M29, M31 | M29 (G), M31 (G) |

### W19_ps: Combinatorial identity transfer (Pset, ~7 levels)

**World promise**: The learner retrieves binomial/counting skills on fresh surface forms.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Fresh Pascal application**: Use Pascal's rule in a new identity | Retrieval of M28 | M28 (T) |
| 2 | **Fresh symmetry application**: Use `choose_symm` in a new context | Retrieval of M30 | M30 (T) |
| 3 | **A sum involving `choose`**: Prove a new sum identity | Retrieval of M31 | M31 (T) |
| 4 | **Binomial theorem specialization**: Set `a = 1, b = 1` in the binomial theorem to get the row-sum | Specialization as a proof move | M29 (R) |
| 5 | **Transfer: Combinatorial vs algebraic proof**: Given a `choose` identity, sketch both a counting argument and an algebraic argument in words | T7 (T) |
| 6 | **Transfer: The binomial theorem as a tool**: Explain how to use the binomial theorem in paper proofs | T7 (T), T10 (T) |
| 7 | **Boss: A standalone combinatorial identity**: An identity requiring multiple techniques | Integration | M28 (G), M29 (G), M31 (G) |

### W20: Three notions of finiteness (Lecture, ~6 levels)

**World promise**: The learner understands the distinctions between `Set.Finite`, `Fintype`, and `Finset`, and can convert between them.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Set.Finite`**: A set can be "finite" in the `Set` sense | `Set.Finite` definition | M35 (I) |
| 2 | **`Fintype`**: A type can be finite via the `Fintype` type class | Review + contrast | M35 (S), M12 (R) |
| 3 | **`Finset`**: A finset is a concrete finite collection | Review + contrast | M35 (S) |
| 4 | **Converting between them**: From `Fintype` to `Finset.univ`, from `Set.Finite` to `Finset.toFinset` | Conversion API | M35 (S) |
| 5 | **When to use which**: Guidelines for choosing the right notion | Practical guidance | M35 (S), C1 (R) |
| 6 | **Boss: A finiteness conversion proof**: Convert between notions in a single proof | Integration of M35 | M35 (G) |

### W21: Finitely supported functions (Lecture, ~8 levels)

**World promise**: The learner understands `Finsupp`, can construct finitely supported functions, and can reason about their support.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **What is `Finsupp`?**: A function that is nonzero on a finite set | `Finsupp` definition | M21 (I) |
| 2 | **`Finsupp.single`**: Construct a function nonzero at exactly one point | Basic construction | M22 (I), N13 (I) |
| 3 | **`Finsupp.support`**: Compute the support of a `Finsupp` | Support finset | M22 (S) |
| 4 | **A `Finsupp` nonzero at two points**: Build and verify | Concretization | E11 (I) |
| 5 | **`Finsupp` vs partial functions**: Why they are different | C11 misconception | C11 (W) |
| 6 | **`Finsupp.sum`**: Sum a function over the support of a `Finsupp` | Big-operator connection | M22 (S) |
| 7 | **Addition of `Finsupp`s**: Prove `(single a m + single b n).support` for `a ne b` | Algebraic structure | M21 (S) |
| 8 | **Boss: A `Finsupp` reasoning chain**: Construct, compute support, sum over support | Integration of M21, M22 | M21 (G), M22 (G) |

### W22: Permutations of finite types (Lecture, ~7 levels)

**World promise**: The learner understands `Equiv.Perm (Fin n)` as the group of permutations, and can connect to factorial counting.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Equiv.Perm` as an equivalence**: A permutation is a bijection from a type to itself | Permutation definition | M36 (I) |
| 2 | **Constructing a specific permutation of `Fin 3`**: Swap two elements | Concrete construction | E18 (I) |
| 3 | **Composition of permutations**: Compose two permutations and verify | Group operation preview | M36 (S) |
| 4 | **The identity permutation**: `Equiv.refl` as the identity | Identity element | M36 (S) |
| 5 | **Counting permutations**: `Fintype.card (Equiv.Perm (Fin n)) = n!` | Connection to factorial | M36 (S), M27 (R) |
| 6 | **`List.permutations` vs `Equiv.Perm`**: Two different notions | C12 misconception | C12 (W) |
| 7 | **Boss: A permutation property**: Prove a property of all permutations of `Fin 3` using exhaustion | Integration of M36, V2 | M36 (G) |

### W23: Matrices as functions over finite types (Lecture, ~8 levels)

**World promise**: The learner understands `Matrix m n alpha` as `m -> n -> alpha`, can construct matrices, and sees that matrix multiplication uses `Finset.sum`.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **`Matrix` as a function**: `Matrix m n alpha` is `m -> n -> alpha` | Matrix definition | M32 (I) |
| 2 | **Constructing a 2x2 matrix**: Build a `Matrix (Fin 2) (Fin 2) Nat` | Concrete construction | E12 (I) |
| 3 | **Accessing entries**: Access `M i j` for specific indices | Function application notation | M32 (S) |
| 4 | **`Matrix.diagonal`**: Construct a diagonal matrix | Diagonal construction | M33 (I) |
| 5 | **`Matrix.transpose`**: Transpose a matrix and verify entries | Transpose | M33 (S) |
| 6 | **Matrix multiplication via `Finset.sum`**: Show that `(A * B) i j = sum k, A i k * B k j` | The big-operator connection | M34 (I) |
| 7 | **Computing a matrix product**: Multiply two specific 2x2 matrices | Concrete computation | M34 (S), E12 (S) |
| 8 | **Boss: A matrix identity**: Prove a property of a specific matrix product | Integration of M32--M34 | M32 (G), M34 (G) |

### W24: Capstone: integration (Boss/Review, ~10 levels)

**World promise**: The learner integrates skills from across the entire course in multi-step proofs. This is the final world.

| # | Level | Dominant lesson | Coverage items |
|---|-------|----------------|---------------|
| 1 | **Warm-up: Fin + Finset**: A proof involving `Fin` elements and finset membership | Cross-module retrieval | M1 (R), M5 (R) |
| 2 | **Warm-up: Counting + big operators**: Count elements of a type and sum a function over them | Cross-module retrieval | M13 (R), M23 (R) |
| 3 | **A sum over `Fintype.univ`**: Express a sum using `Finset.univ` and `Fintype.card` | Integration | M12 (R), M23 (R) |
| 4 | **Pigeonhole + big operators**: Use pigeonhole to prove a result about sums | Multi-technique proof | M39 (R), M23 (R) |
| 5 | **Binomial coefficient + cardinality**: Prove that `Finset.card (powerset s) = 2 ^ card s` relates to binomial coefficients | Cross-module connection | M11 (R), M27 (R) |
| 6 | **Matrix trace as a sum**: Define and compute the trace of a matrix as `sum i, M i i` | Big-operator + matrix integration | M34 (R), M23 (R) |
| 7 | **A `Finsupp` sum identity**: Prove a property relating `Finsupp.sum` to `Finset.sum` | Finsupp + big-op integration | M22 (R), M23 (R) |
| 8 | **Transfer: Describe the finite-math toolkit**: Write in words what tools the course gave you | T8 (G) |
| 9 | **Transfer: A paper-proof exercise**: Given a Lean statement about finite sums, write the paper proof | T2 (G), T10 (G) |
| 10 | **Boss: The grand integration**: A multi-step proof using finsets, cardinality, big operators, and at least one counting identity | Final integration of all modules | Full course (G) |

---

## 6. Inventory release plan

### Tactics

| Tactic | World introduced | Notes |
|--------|-----------------|-------|
| `omega` | W1 (available from start, used explicitly) | NNG4 baseline; highlight in finset arithmetic |
| `fin_cases` | W2.1 | New tactic. Teach explicitly. |
| `decide` | W2.3 | New tactic. Teach explicitly. |
| `norm_num` | W2.5 | New tactic. Teach explicitly. |
| `simp` (with lemma lists) | W6.4 | New tactic. Teach with finset lemma families. |
| `ext` | W7.5 | New tactic. Teach for finset equality. |
| `ring` | W15.4 | New tactic. Teach for algebraic big-op goals. |
| `congr` | W15.7 | New tactic. Teach for big-operator manipulation. |
| `calc` | W14.4 | New tactic pattern. Teach for equational chaining. |
| `conv` | W16.5 | New tactic. Teach for rewriting under binders. |
| `gcongr` | W16.6 | New tactic. Teach for monotone inequalities. |
| `push_cast` | W19.2 | New tactic. Teach for type coercion goals. |

**Hidden tactics** (available via `NewHiddenTactic` from the start):
- `rwa` (rewrite + assumption)
- `rewrite` (alias for `rw`)
- `simp_all`
- `tauto`
- `trivial`
- `contradiction`

**NNG4 baseline tactics** (available from W1):
- `rw`, `exact`, `apply`, `intro`, `cases`, `constructor`, `have`, `use`, `assumption`, `induction`, `rcases`, `obtain`, `refine`, `by_contra`, `exfalso`, `left`, `right`

### Theorems / Definitions

Theorems and definitions are released world-by-world as they are taught. The key principle: **a theorem enters the inventory in the level where the learner first proves or uses it**. No "free theorems" without justification.

**TheoremTab groupings:**
- `Fin` tab: `Fin.val`, `Fin.mk`, `Fin.last`, `Fin.castSucc`, `Fin.succ`, `finZeroElim`
- `List` tab: `List.mem`, `List.length`, `List.map`, `List.filter`, `List.Nodup`, `List.Perm`
- `Multiset` tab: `Multiset.card`, `Multiset.map`, `Multiset.dedup`
- `Finset` tab: `Finset.mem_insert`, `mem_union`, `mem_inter`, `mem_sdiff`, `mem_filter`, `mem_image`, `Finset.ext_iff`
- `Finset.card` tab: `card_empty`, `card_singleton`, `card_insert_of_not_mem`, `card_union_add_card_inter`, `card_filter_le_card`
- `BigOp` tab: `sum_empty`, `sum_singleton`, `sum_cons`, `sum_insert`, `sum_union`, `sum_range_succ`, `sum_filter`, `sum_comm`, `prod_empty`, `prod_range_succ`
- `Fintype` tab: `Fintype.card_fin`, `Fintype.card_prod`, `Fintype.card_sum`, `Fintype.card_fun`
- `Choose` tab: `Nat.choose`, `Nat.choose_succ_succ`, `Nat.choose_symm`, `Nat.choose_zero_right`, `Nat.choose_self`, `Nat.factorial`

---

## 7. Boss map

| World | Boss level | What it tests | Seeded by levels |
|-------|-----------|---------------|-----------------|
| W1 | W1.8 | Universally quantified property of `Fin 4`: uses `Fin.val`, coercion, `omega` | W1.1--W1.7 |
| W2 | W2.8 | Property of `Fin 5`: uses `fin_cases`, `norm_num`, `omega` | W2.1--W2.7 |
| W3 | W3.8 | List manipulation: `map`, `filter`, `length`, membership | W3.1--W3.7 |
| W4 | W4.9 | Hierarchy trace: list -> multiset -> finset with cardinality comparison | W4.1--W4.8, W3.* |
| W5 | W5.8 | Three constructions of the same finset shown equal | W5.1--W5.7 |
| W6 | W6.9 | Multi-step membership reasoning with `simp` and case splitting | W6.1--W6.8 |
| W7 | W7.10 | De Morgan for finsets: `s \ (t cap u) = (s \ t) cup (s \ u)` | W7.1--W7.9 |
| W8 | W8.8 | Filter-image-membership-cardinality chain | W8.1--W8.7 |
| W9 | W9.9 | Union + intersection cardinality of specific finsets | W9.1--W9.8 |
| W10 | W10.9 | Non-trivial finset induction proof | W10.1--W10.8 |
| W10_ps | W10_ps.8 | Multi-step finset reasoning (4+ moves) | W10_ps.1--W10_ps.7, all of Module C |
| W11 | W11.8 | `Fintype.card` of compound type | W11.1--W11.7 |
| W12 | W12.10 | Counting + pigeonhole on compound type | W12.1--W12.9 |
| W12_ps | W12_ps.7 | Multi-step counting argument | W12_ps.1--W12_ps.6 |
| W13 | W13.9 | Multi-step big-sum simplification | W13.1--W13.8 |
| W14 | W14.9 | Sum identity by induction | W14.1--W14.8 |
| W15 | W15.8 | Algebraic big-operator identity (sum + product) | W15.1--W15.7 |
| W16 | W16.9 | Splitting + reindexing proof | W16.1--W16.8 |
| W16_ps | W16_ps.8 | Multi-step big-operator proof | W16_ps.1--W16_ps.7 |
| W17 | W17.7 | Factorial identity by induction | W17.1--W17.6 |
| W18 | W18.9 | Binomial coefficient identity using Pascal's rule | W18.1--W18.8 |
| W19 | W19.10 | Combined binomial identity | W19.1--W19.9 |
| W19_ps | W19_ps.7 | Standalone combinatorial identity | W19_ps.1--W19_ps.6 |
| W21 | W21.8 | Finsupp reasoning chain | W21.1--W21.7 |
| W22 | W22.7 | Permutation property of `Fin 3` | W22.1--W22.6 |
| W23 | W23.8 | Matrix product identity | W23.1--W23.7 |
| W24 | W24.10 | Grand integration: finsets + cardinality + big ops + counting identity | All worlds |

---

## 8. Transfer and retrieval plan

### Core proof moves

| Move | Introduced | Supported practice | Retrieval | Fresh surface | Paper transfer |
|------|-----------|-------------------|-----------|--------------|---------------|
| Unfolding a definition (V1) | W1.4 | W2, W5 | W6, W8 | W10_ps, W16_ps | W7 conclusion |
| Case exhaustion on `Fin` (V2) | W2.1 | W2.2--W2.4, W3_ex | W12_ex, W22 | W24.1 | W3_ex.6 |
| `Nat` induction on sums (V3) | W14.3 | W14.4--W14.8 | W16_ps.1 | W19 | W14_ex.6 |
| Finset induction (V4) | W10.2 | W10.3--W10.5 | W10_ps.5 | W16_ps.2 | W10.7 comparison |
| Membership rewriting (V5) | W6.1 | W6.2--W6.8 | W7, W8 | W10_ps.1 | W10_ps.6 |
| `ext` for finset equality (V6) | W7.5 | W7.6, W7.9 | W10_ps.3 | W16_ps | W7 conclusion |
| Pigeonhole (V16) | W12.6 | W12.7--W12.9 | W12_ps.2 | W24.4 | W12 conclusion, W12_ps.5 |
| Big-operator peeling (V11) | W14.2 | W14.3--W14.8 | W16_ps.1 | W19 | W14_ex.6 |
| Algebraic manipulation in sums (V20) | W15.5 | W15.6, W16 | W16_ps.3 | W19 | W16_ps.7 |

### Core concepts

| Concept | Introduced | Concretized | Counterexampled | Retrieved | Transferred |
|---------|-----------|-------------|-----------------|-----------|-------------|
| `Fin n` | W1.1 | W3_ex | W1.4 (Fin 0) | W11, W22, W24 | W3_ex.6 |
| `Finset` | W5 | W8_ex | W5.7 (vs Set) | W9--W16 | W10_ps.6--7 |
| List/Multiset/Finset hierarchy | W3--W4 | W4_ex | W4.6 (info loss) | W20 | W4_ex.5 |
| `Fintype.card` | W11.3 | W12_ex | W11.7 (Nat) | W17, W22, W24 | W12_ps.6 |
| `Finset.sum` | W13.1 | W14_ex | W13.6 (AddCommMonoid) | W15--W19, W24 | W14_ex.6, W16_ps.6--7 |
| `Nat.choose` | W18.1 | W18_ex | W18.3 (k > n) | W19, W19_ps | W19.9, W19_ps.5--6 |
| Pigeonhole | W12.6 | W12.9 | -- | W12_ps, W24 | W12 conclusion, W12_ps.5 |

---

## 9. Misconception plan

| Misconception | Where first warned | Where reinforced | Where tested |
|--------------|-------------------|-----------------|-------------|
| C1: Finset is not Set | W5.7 | W11, W20 | W10_ps (fresh surface) |
| C2: DecidableEq requirement | W5.6 | W13.6 (AddCommMonoid) | -- |
| C3: List/Multiset/Finset hierarchy | W4.4 | W4.6, W4_ex | W10_ps, W20 |
| C4: card counts without multiplicity | W4.7 | W9.4 | W8.7 |
| C5: Fin 0 empty, Fin 1 singleton | W1.4--W1.5 | W3_ex.1 | W2.8 |
| C6: Fin n is 0-indexed | W1.6 | W3_ex | W2 levels |
| C7: insert is idempotent | W6.6 | W9.4 | W10_ps |
| C8: sum needs AddCommMonoid | W13.6 | -- | -- |
| C9: range n is exclusive | W9.6 | W14.1, W14.8 | W16_ps |
| C10: choose n k = 0 for k > n | W18.3 | W18_ex | W19_ps |
| C11: Finsupp vs partial function | W21.5 | -- | -- |
| C12: Equiv.Perm vs List.permutations | W22.6 | -- | -- |

---

## 10. Granularity plan

### Per-level novelty budget

Each level introduces at most **one** new burden (new math, new proof move, new tactic, or new notation). Everything else is held familiar. This is enforced across the entire course, not relaxed as the learner advances.

### Key novelty-hotspot resolutions

| Potential hotspot | Resolution |
|------------------|-----------|
| "Intro to `Fin n`" (new math + new notation + new tactic) | Split into W1.1 (definition), W1.6 (coercion notation), W2.1 (`fin_cases` tactic) |
| "Intro to `Finset.sum`" (new math + new notation) | Borderline OK: new math + new notation together since proof move is familiar. W13.1 teaches both. |
| "Binomial theorem" (new math + multi-step induction + `ring`) | Split into W18 (binomial coefficients + Pascal), then W19 (binomial theorem). `ring` taught separately in W15.4. |
| "Matrix multiplication via `Finset.sum`" (new math + double sum) | W16.4 teaches double sums first. W23.6 introduces matrix mul definition. W23.7 does the computation. |
| "Finset induction" (new induction principle + new tactic pattern) | W10.1 reviews `Nat` induction. W10.2 introduces `Finset.induction_on`. W10.3 practices. |

### World-scale granularity checks

Every world passes these checks:
- **Single center of gravity**: The boss is recognizably about the world's topic.
- **Coherent intro**: The world introduction can explain the world's purpose in 2--3 sentences.
- **No unrelated theorem families**: All levels share a common family or cluster.

---

## 11. Major risks

1. **Type class overwhelm**: `Finset` operations require `DecidableEq`, `AddCommMonoid`, etc. The plan mitigates by teaching each type class constraint individually (C2 in W5, C8 in W13) and not frontloading them.

2. **Coercion confusion**: Moving between `Fin n`, `Nat`, `Finset`, `Set`, and `Multiset` involves many coercions. Each coercion boundary is an explicit teaching moment (W1.6 for `Fin -> Nat`, W4 for the hierarchy, W20 for the three notions).

3. **`simp` over-reliance**: Many finset goals can be solved by `simp` with the right lemma set. The plan mitigates by (a) not introducing `simp` until W6, (b) requiring manual proofs alongside `simp` proofs in W6.5, and (c) varying proof moves across worlds.

4. **Scope creep into combinatorics**: The boundary between "counting identities" (in scope) and "combinatorics" (Course 32) is maintained by stopping at the binomial theorem, row sums, and Vandermonde. Hall's marriage theorem, Catalan numbers, and Ramsey-type results are excluded.

5. **`Finsupp`/`Matrix`/`Perm` depth**: Module G is intentionally light -- a taste rather than a deep treatment. Each capstone world has ~7--8 levels, not full-depth coverage. The risk is that the taste feels shallow. Mitigation: each world has a concrete example and a meaningful boss.

6. **Big-operator module length**: Module E has 4 lecture worlds + 1 example + 1 pset = 6 worlds. This is appropriate given that big operators are the payoff layer of the course, but the module must be paced carefully to avoid fatigue. Mitigation: the example world (W14_ex) breaks the lecture sequence with computation.

7. **Natural number division**: The sum formula `sum_{i=0}^{n-1} i = n(n-1)/2` involves natural-number division, which behaves differently from integer division. This must be handled carefully (either by using `2 * sum = n * (n-1)` or by introducing `push_cast` early).

---

## 12. Recommended first three worlds to author

1. **W1: What is `Fin n`?** -- This is the entry point. It depends on nothing and introduces the foundational type. It tests the basic authoring workflow without complex dependencies.

2. **W3: Lists: construction and operations** -- This can be authored in parallel with W2 since it depends only on W1. It establishes the bottom layer of the hierarchy that the rest of the course builds on.

3. **W2: Computing with `Fin`** -- This depends on W1 and introduces the first genuinely new tactics (`fin_cases`, `decide`, `norm_num`). Authoring it second (or in parallel with W3) lets the author validate the tactic-introduction workflow.

After these three, the next priority is W4 (Multisets and hierarchy) followed by W5 (Constructing finsets), which unlocks the entire Module C chain.

---

## Appendix: World summary table

| World | Module | Type | Levels | Boss | Dependencies |
|-------|--------|------|--------|------|-------------|
| W1 | A | Lecture | 8 | W1.8 | -- |
| W2 | A | Lecture | 8 | W2.8 | W1 |
| W3_ex | A | Example | 6 | -- | W2 |
| W3 | B | Lecture | 8 | W3.8 | W1 |
| W4 | B | Lecture | 9 | W4.9 | W3 |
| W4_ex | B | Example | 5 | -- | W4 |
| W5 | C | Lecture | 8 | W5.8 | W4 |
| W6 | C | Lecture | 9 | W6.9 | W5 |
| W7 | C | Lecture | 10 | W7.10 | W6 |
| W8 | C | Lecture | 8 | W8.8 | W7 |
| W8_ex | C | Example | 7 | -- | W8 |
| W9 | C | Lecture | 9 | W9.9 | W8 |
| W10 | C | Lecture | 9 | W10.9 | W9 |
| W10_ps | C | Pset | 8 | W10_ps.8 | W10 |
| W11 | D | Lecture | 8 | W11.8 | W10, W2 |
| W12 | D | Lecture | 10 | W12.10 | W11 |
| W12_ex | D | Example | 5 | -- | W12 |
| W12_ps | D | Pset | 7 | W12_ps.7 | W12 |
| W13 | E | Lecture | 9 | W13.9 | W10 |
| W14 | E | Lecture | 9 | W14.9 | W13 |
| W14_ex | E | Example | 6 | -- | W14 |
| W15 | E | Lecture | 8 | W15.8 | W14 |
| W16 | E | Lecture | 9 | W16.9 | W15 |
| W16_ps | E | Pset | 8 | W16_ps.8 | W16 |
| W17 | F | Lecture | 7 | W17.7 | W16, W12 |
| W18 | F | Lecture | 9 | W18.9 | W17 |
| W18_ex | F | Example | 6 | -- | W18 |
| W19 | F | Lecture | 10 | W19.10 | W18 |
| W19_ps | F | Pset | 7 | W19_ps.7 | W19 |
| W20 | G | Lecture | 6 | W20.6 | W11 |
| W21 | G | Lecture | 8 | W21.8 | W20, W16 |
| W22 | G | Lecture | 7 | W22.7 | W20, W12 |
| W23 | G | Lecture | 8 | W23.8 | W22, W16 |
| W24 | G | Boss/Review | 10 | W24.10 | W23, W21, W19 |
| **Total** | | | **~205** | | |

---

## Appendix: Coverage closure verification

Every coverage item from the COVERAGE_MAP.md is assigned to at least one world:

**MATH items**: M1--M40 all covered. M1--M3 in W1--W2. M4 in W2. M5--M11 in W5--W9. M12--M14 in W11--W12. M15 in W5. M16--M20 in W3--W4. M21--M22 in W21. M23--M26 in W13--W16. M27--M31 in W17--W19. M32--M34 in W23. M35 in W20. M36--M37 in W22. M38 in W16. M39--M40 in W12.

**MOVE items**: V1--V20 all covered. Each first appears in its assigned world and is practiced, retrieved, and transferred per the transfer plan (Section 8).

**LEAN items**: L1--L18 all covered. Each tactic is introduced in its assigned world and available thereafter.

**NOTATION items**: N1--N13 all covered. Each notation is taught in its assigned world.

**MISCONCEPTION items**: C1--C12 all covered per the misconception plan (Section 9).

**TRANSFER items**: T1--T10 all covered. Transfer moments are distributed across example worlds, pset worlds, and boss conclusions.

**EXAMPLE items**: E1--E19 all covered. Each example appears in the assigned example world or as a level within a lecture world.
