# Coverage Map: finite_math

## Course identity

**Catalog position**: Course 1 (Foundations block).
**Prerequisites**: NNG4-level Lean fluency. No serious mathematics.
**Scope**: Finite-object infrastructure: `Fin`, `Fintype`, `Finset`, finite sets as subtypes, lists versus multisets, permutations of lists, finitely supported functions, finite products of finsets, matrices over finite index types, big operators, binomial coefficients, factorials, finite sums/products, and counting identities.
**Explicit exclusions**: graph theory, Ramsey theory, additive combinatorics.
**Current state**: Stub only (one Welcome level proving `True`). This is a pre-authoring coverage map.

---

## 1. Coverage matrix summary

### Axis: MATH (definitions, objects, theorem families)

| # | Item | Importance | Notes |
|---|------|-----------|-------|
| M1 | `Fin n` as `{ i : Nat // i < n }` | core | The foundational finite index type |
| M2 | `Fin.val`, `Fin.mk`, `Fin.last`, `Fin.castSucc`, `Fin.succ` | core | Constructors and navigation within `Fin` |
| M3 | `Fin 0` is empty; `Fin 1` is a singleton | core | Boundary cases, `finZeroElim` |
| M4 | Arithmetic on `Fin n` (addition, subtraction mod n) | supporting | Modular arithmetic flavor |
| M5 | `Finset α` as `{val : Multiset α // val.Nodup}` | core | The central finite-set type |
| M6 | `Finset.empty`, `Finset.singleton`, `Finset.cons`, `Finset.insert` | core | Constructing finsets |
| M7 | `Finset.union`, `Finset.inter`, `Finset.sdiff`, `Finset.disjUnion` | core | Set operations |
| M8 | `Finset.filter`, `Finset.image`, `Finset.map` | core | Transforming finsets |
| M9 | `Finset.card` and cardinality lemmas | core | `card_empty`, `card_singleton`, `card_insert_of_not_mem`, `card_union_add_card_inter` |
| M10 | `Finset.range n`, `Finset.Icc`, `Finset.Ico` | core | Interval finsets |
| M11 | `Finset.powerset`, `Finset.product` | supporting | Power set and Cartesian product of finsets |
| M12 | `Fintype α` (the type class: `Finset.univ` contains all elements) | core | The type class that makes a type finite |
| M13 | `Fintype.card α` and its relationship to `Finset.univ.card` | core | Counting elements of a finite type |
| M14 | `Fintype` instances: `Fin n`, `Bool`, `Unit`, products, sums, subtypes, function types | core | Where finiteness propagates |
| M15 | `Decidable` and `DecidableEq` as prerequisites for `Finset` membership | supporting | Why `Finset` needs decidable equality |
| M16 | `List α` basic API: `nil`, `cons`, `append`, `length`, `mem`, `map`, `filter` | core | Lists as the concrete sequential type |
| M17 | `List.Nodup`, `List.Perm`, `List.dedup` | core | Permutations and duplicates in lists |
| M18 | `Multiset α` as `Quot (List.Perm)` | core | The unordered-with-multiplicity type |
| M19 | `Multiset.card`, `Multiset.map`, `Multiset.filter`, `Multiset.dedup` | core | Multiset operations |
| M20 | The `List -> Multiset -> Finset` pipeline and `toFinset` | core | The three-layer hierarchy |
| M21 | `Finsupp α M` (finitely supported functions) | core | Functions nonzero on a finite set |
| M22 | `Finsupp.single`, `Finsupp.support`, `Finsupp.sum` | core | Finsupp construction and operations |
| M23 | `Finset.sum` and `Finset.prod` (big operators) | core | Summing/multiplying over a finset |
| M24 | Big operator lemmas: `sum_empty`, `sum_cons`, `sum_singleton`, `sum_union`, `sum_filter` | core | The basic big-operator API |
| M25 | `Finset.sum` over `range`: telescoping, splitting, reindexing | core | Computational big-operator patterns |
| M26 | `prod_comm`, `sum_comm` (interchange of summation order) | supporting | Double sums/products |
| M27 | `Nat.factorial`, `Nat.choose`, `Nat.descFactorial` | core | Combinatorial counting functions |
| M28 | Pascal's rule: `Nat.choose_succ_succ` | core | The recursion for binomial coefficients |
| M29 | Binomial theorem: `Commute.add_pow` or `Finset.sum` form | core | Capstone counting identity |
| M30 | `Nat.choose_symm`, `Nat.choose_zero_right`, `Nat.choose_self` | supporting | Basic binomial identities |
| M31 | Vandermonde convolution / sum of `choose` identities | supporting | Counting identity family |
| M32 | `Matrix m n α` as `m -> n -> α` over finite index types | supporting | Matrices as functions |
| M33 | `Matrix.of`, `Matrix.diagonal`, `Matrix.transpose` | supporting | Basic matrix constructions |
| M34 | `Matrix.mul` defined via `Finset.sum` | supporting | Connecting big operators to linear algebra preview |
| M35 | `Set.Finite` vs `Fintype` vs `Finset` distinctions | core | The three notions of finiteness |
| M36 | `Equiv.Perm (Fin n)` (permutations as equivalences) | supporting | Permutations of finite types |
| M37 | `List.permutations` and `List.permutations'` | supporting | Enumerating permutations |
| M38 | `Finset.sum_ite`, conditional sums and indicator-style lemmas | supporting | Splitting sums by predicate |
| M39 | Pigeonhole principle: `Fintype.exists_ne_map_eq_of_card_lt` and variants | core | Classic counting argument |
| M40 | Double counting / bijectivity-based cardinality arguments | supporting | Proof strategy family |

### Axis: MOVE (proof strategies and proof shapes)

| # | Item | Importance | Notes |
|---|------|-----------|-------|
| V1 | Unfolding a definition to reveal structure | core | `simp only [Finset.mem_union]`, `unfold`, `change` |
| V2 | Case splitting on `Fin` elements (exhaustion over `Fin n` for small n) | core | `fin_cases`, `interval_cases`, `decide` |
| V3 | Induction on `Nat` to prove properties of `Finset.range` sums | core | `induction n with ...` |
| V4 | Induction on `Finset` via `Finset.induction_on` | core | The finset-specific induction principle |
| V5 | Rewriting with membership lemmas (`mem_union`, `mem_filter`, `mem_image`) | core | Goal-state transformation via `rw`/`simp` |
| V6 | Using `ext` to prove finset equality | core | Two finsets are equal iff they have the same members |
| V7 | Using `Decidable.em` or `Classical.em` for case analysis on membership | supporting | `a \in s \lor a \notin s` |
| V8 | Choosing a witness from a nonempty finset | core | `Finset.Nonempty` -> extracting an element |
| V9 | Contradiction via cardinality: `card = 0` means empty | supporting | Pigeonhole-style reasoning |
| V10 | Building a `Finset` by explicit construction (listing elements) | core | `{1, 2, 3}` notation; `Finset.cons` |
| V11 | Splitting a `Finset.sum` at a boundary (e.g., sum over `range (n+1)`) | core | `sum_range_succ`, peeling off the last term |
| V12 | Reindexing a sum or product | supporting | `sum_bij`, `sum_equiv` |
| V13 | Using `simp` with finset lemmas to simplify membership goals | core | Identifying the right simp set |
| V14 | Proving subset relations: `s \subseteq t` by intro + membership | core | `intro x hx; ...` |
| V15 | Using `Finset.card_le_card` from subset to get cardinality inequalities | supporting | Cardinality monotonicity |
| V16 | Applying the pigeonhole principle as a proof move | core | Recognizing when to use it |
| V17 | Converting between `List.Perm` and `Multiset` equality | supporting | The quotient bridge |
| V18 | Using `have` to break a proof into named subgoals | core | Proof structuring (NNG4 review) |
| V19 | Recursive/inductive construction of a function or proof | core | Building objects over `Fin n` by recursion |
| V20 | Algebraic manipulation inside big-operator goals | supporting | `sum_add_sum`, distributing multiplication |

### Axis: LEAN (tactics, commands, proof-state manipulations)

| # | Item | Importance | Notes |
|---|------|-----------|-------|
| L1 | `simp` with finset-specific lemma sets | core | `simp [Finset.mem_union, Finset.mem_filter]` |
| L2 | `ext` for proving set/finset equality | core | Extensionality tactic |
| L3 | `decide` for decidable propositions on small finite types | core | Automated verification for `Fin n` goals |
| L4 | `fin_cases` for exhaustive case analysis on `Fin n` | core | New tactic for this course |
| L5 | `omega` for natural number arithmetic goals | core | NNG4 baseline, but heavily used here |
| L6 | `norm_num` for numeric computation | core | Evaluating `Nat.choose`, `Nat.factorial` |
| L7 | `ring` for commutative ring goals in sums/products | supporting | Algebraic normalization |
| L8 | `induction` with custom induction principles (`Finset.induction_on`) | core | Non-standard induction |
| L9 | `rcases` / `obtain` for destructuring | core | NNG4 baseline, but deeper use here |
| L10 | `use` for providing witnesses | core | NNG4 baseline |
| L11 | `congr` for matching function applications | supporting | Big-operator goal manipulation |
| L12 | `conv` for targeted rewriting inside binders | supporting | Rewriting under `sum`/`prod` |
| L13 | `rfl` and `Eq.subst` for equality reasoning | core | NNG4 baseline |
| L14 | `calc` for multi-step equational reasoning | supporting | Chaining cardinality/sum equalities |
| L15 | `push_cast` / `Nat.cast` for moving between `Nat` and other types | supporting | When sums land in `Int` or `Rat` |
| L16 | `gcongr` for monotone inequality goals | supporting | Bounding sums |
| L17 | `refine` for partially filling in terms | supporting | NNG4 baseline, more sophisticated use |
| L18 | `constructor` for splitting conjunctions | core | NNG4 baseline |
| L19 | `apply?` / `exact?` as search tools (for player discoverability) | supporting | Teaching theorem search |

### Axis: NOTATION

| # | Item | Importance | Notes |
|---|------|-----------|-------|
| N1 | `{a, b, c}` as `Finset` literal notation | core | `insert a (insert b (singleton c))` |
| N2 | `a \in s` for `Finset.mem` | core | Membership notation |
| N3 | `s \cup t`, `s \cap t`, `s \ t` for finset operations | core | Set operation notation |
| N4 | `s \subseteq t` for finset subset | core | Subset notation |
| N5 | `\sum x in s, f x` (big sum notation) and `\prod x in s, f x` | core | Big operator notation |
| N6 | `Finset.range n` vs `Finset.Icc a b` vs `Finset.Ico a b` | core | Different interval notations |
| N7 | `\|s\|` or `s.card` for cardinality | supporting | Cardinality notation |
| N8 | Coercion `Fin n -> Nat` (the `\uparrow` / `\u2191` arrow) | core | Coercion notation |
| N9 | `fun i : Fin n => ...` for functions on finite types | core | Lambda over `Fin` |
| N10 | `Finset.univ` (implicit from `Fintype` instance) | core | The universal finset |
| N11 | `::` for `List.cons` vs `Finset.cons` | supporting | Disambiguation |
| N12 | `++` for `List.append` | supporting | List concatenation |
| N13 | `Finsupp.single a m` notation | supporting | Finitely supported function literal |

### Axis: MISCONCEPTION

| # | Item | Importance | Notes |
|---|------|-----------|-------|
| C1 | `Finset` is NOT `Set`: you cannot use `Set` lemmas on `Finset` without coercion | core | The most common confusion |
| C2 | `Finset` requires `DecidableEq`: membership is decidable, not classical | core | Why `Finset` membership is computable |
| C3 | `List` has order and duplicates; `Multiset` has duplicates but no order; `Finset` has neither | core | The hierarchy misconception |
| C4 | `Finset.card` counts with multiplicity removed (because `Nodup`) | supporting | Card of a finset vs length of a list |
| C5 | `Fin 0` is empty, not a singleton; `Fin 1` is a singleton, not "1" | core | Off-by-one in finite types |
| C6 | `Fin n` elements are natural numbers < n, not elements 1..n | core | Zero-indexing confusion |
| C7 | `insert a s` does nothing if `a \in s` already (idempotence) | supporting | Expecting `card` to grow |
| C8 | `Finset.sum` requires an `AddCommMonoid`, not just `Add` | supporting | Type class confusion |
| C9 | `\sum x in Finset.range n, f x` sums over `0, 1, ..., n-1`, not `1, ..., n` | core | Range is exclusive at the top |
| C10 | `Nat.choose n k = 0` when `k > n`, not an error | supporting | Boundary behavior of choose |
| C11 | `Finsupp` is not the same as a partial function; it tracks the support explicitly | supporting | Finsupp vs partial function |
| C12 | Permutations of `Fin n` are equivalences (`Equiv.Perm`), not lists | supporting | Two notions of permutation |

### Axis: TRANSFER

| # | Item | Importance | Notes |
|---|------|-----------|-------|
| T1 | Counting elements of a finite set by case analysis (correspond to `fin_cases` / `decide`) | core | Paper-proof: "There are n elements, namely..." |
| T2 | Induction on finite sums: peel off last term, use induction hypothesis | core | Paper-proof: "By induction, the sum up to n equals..." |
| T3 | Subset argument to bound cardinality | core | Paper-proof: "Since S is a subset of T, |S| <= |T|" |
| T4 | Inclusion-exclusion as an additive identity | core | Paper-proof: "|A union B| = |A| + |B| - |A inter B|" |
| T5 | Pigeonhole as a proof technique | core | Paper-proof: "There are n+1 objects in n boxes, so..." |
| T6 | Double counting: count the same set two ways | supporting | Paper-proof: "We count pairs (x,y) in two ways..." |
| T7 | Binomial coefficient identities via algebraic or combinatorial proof | core | Paper-proof: Pascal's rule, Vandermonde, etc. |
| T8 | Stating what "finite" means in a mathematical context | core | Paper-proof: "Let S be a finite set..." |
| T9 | Translating between "list of distinct elements" and "finite set" | supporting | Paper-proof: connecting enumeration to set theory |
| T10 | Reading a big-operator expression as ordinary sigma notation | core | Paper-proof: "\sum_{i=0}^{n-1} f(i)" |

### Axis: EXAMPLE (concrete mathematical objects)

| # | Item | Importance | Notes |
|---|------|-----------|-------|
| E1 | `Fin 3` as `{0, 1, 2}` -- explicit computation of all elements | core | Concretization of `Fin` |
| E2 | `Finset.range 5` as `{0, 1, 2, 3, 4}` -- explicit enumeration | core | Concretization of `range` |
| E3 | `({1, 2, 3} : Finset Nat)` -- a literal finset of naturals | core | Concretization of `Finset` |
| E4 | Sum of first n natural numbers: `\sum i in range n, i = n*(n-1)/2` | core | Classic induction example |
| E5 | Sum of geometric series over a finset | supporting | Big-operator computation |
| E6 | `Nat.choose 5 2 = 10` -- explicit computation | core | Concretization of `choose` |
| E7 | `Nat.factorial 5 = 120` -- explicit computation | supporting | Concretization of `factorial` |
| E8 | Power set of `{1, 2, 3}` has 8 elements | supporting | Concretization of `powerset` |
| E9 | `Fin 3 -> Bool` has `2^3 = 8` elements (counting function types) | supporting | Concretization of `Fintype.card` for function types |
| E10 | The empty finset and its properties | core | Boundary example |
| E11 | A `Finsupp` that is nonzero at exactly two points | supporting | Concretization of `Finsupp` |
| E12 | A 2x2 matrix over `Fin 2` -- matrix as a function `Fin 2 -> Fin 2 -> Nat` | supporting | Concretization of `Matrix` |
| E13 | `Bool` as `Fintype` with `Fintype.card Bool = 2` | supporting | Simplest nontrivial finite type |
| E14 | Counterexample: `Nat` is NOT a `Fintype` | core | Why finiteness is a condition |
| E15 | Counterexample: `List` with duplicates vs the `Finset` it produces | core | Why `toFinset` can lose information |
| E16 | Counterexample: `Finset.range 0 = \emptyset` -- the empty range | supporting | Boundary counterexample |
| E17 | Pascal's triangle rows as explicit `Nat.choose` computations | core | Visual + computational concretization |
| E18 | `Equiv.Perm (Fin 3)` -- the six permutations of three elements | supporting | Concretization of permutations |
| E19 | Product of `{1, 2} \times {a, b, c}` as a finset of pairs | supporting | Concretization of `Finset.product` |

---

## 2. Core uncovered items

Since the course has no authored content, **all items above are uncovered**. The following items are flagged as highest priority because they are both core and prerequisite to many later items:

1. **M1-M3**: `Fin n` definition and boundary cases -- everything else depends on understanding `Fin`
2. **M5-M7**: `Finset` definition and basic operations -- the central type of the course
3. **M12-M13**: `Fintype` type class and `card` -- the bridge from types to counting
4. **M16-M20**: The List/Multiset/Finset hierarchy -- essential structural understanding
5. **M23-M25**: Big operators -- the payoff layer that makes finite objects usable
6. **V1-V6**: The six core proof moves (unfolding, case splitting, induction, rewriting, ext, membership)
7. **L1-L6**: The six core tactics (`simp`, `ext`, `decide`, `fin_cases`, `omega`, `norm_num`)
8. **C1-C3**: The three most dangerous misconceptions (Finset vs Set, DecidableEq, hierarchy)

---

## 3. Weakly covered items

Not applicable (no content exists). Once authoring begins, this section should track items that are mentioned but never practiced, or introduced but never retrieved.

---

## 4. Example coverage gaps

All major definitions require concrete examples. The following pairings are essential and must appear in the course:

| Definition | Required concretization | Required counterexample |
|-----------|------------------------|------------------------|
| `Fin n` | Enumerate `Fin 3`, compute with `Fin.val` (E1) | `Fin 0` is empty (E1, C5) |
| `Finset` | Build `{1,2,3}`, check membership (E3) | List with duplicates -> `toFinset` loses info (E15) |
| `Fintype` | `Bool`, `Fin n`, products (E13, E9) | `Nat` has no `Fintype` instance (E14) |
| `Multiset` | Same list, different order, same multiset | Multiset with duplicates vs Finset without |
| `Finset.range` | `range 5 = {0,1,2,3,4}` (E2) | `range 0 = \emptyset` (E16); range is exclusive (C9) |
| `Nat.choose` | `choose 5 2 = 10` (E6) | `choose 3 5 = 0` (C10) |
| `Finset.sum` | Sum of `range n` (E4) | Empty sum = 0 (E10) |
| `Finsupp` | A function nonzero at {2, 5} (E11) | vs a partial function (C11) |
| `Matrix` | A 2x2 matrix (E12) | -- |
| `Equiv.Perm` | The 6 permutations of `Fin 3` (E18) | vs `List.permutations` output (C12) |

---

## 5. Redundant items

Not applicable (no content exists). The main redundancy risk to watch during authoring:

- **`simp` for membership goals** could become repetitive if every finset-operation level is just "simp with the right lemma." Vary the proof moves.
- **Small `Fin n` exhaustion** could become tedious if overused. Use `decide` for trivial cases and save `fin_cases` for pedagogically interesting ones.
- **`card` computations** can become rote. Each cardinality level should introduce a new counting principle, not just a new number.

---

## 6. Granularity defects

### Pre-authoring granularity concerns:

**Risk of overbroad worlds:**
- A "Finset operations" world that tries to cover union, intersection, difference, filter, image, and subset all at once. These should be at least two worlds (basic construction + set operations, then filter/image/map).
- A "Big operators" world that introduces both `sum` and `prod` notation, the basic API, algebraic manipulation, and inductive proofs all at once. Big operators deserve 2-3 worlds.

**Risk of overfine levels:**
- Separate levels for `mem_union`, `mem_inter`, `mem_sdiff` that differ only by which set operation is used. These should be consolidated: one level per operation is fine, but three levels that all have the same proof shape (`intro x; simp [mem_*]`) are redundant.

**Risk of missing micro-move isolation:**
- The `Finset.induction_on` proof move is structurally different from `Nat.induction` and must be explicitly taught before any boss uses it.
- Reindexing a sum (`sum_bij`, `sum_equiv`) is a hard move that must be isolated before it appears in a boss.

---

## 7. Novelty hotspots

### Items that introduce novelty on multiple axes simultaneously (must be split):

| Potential level | New math | New move | New Lean | New notation | Verdict |
|----------------|----------|----------|----------|-------------|---------|
| "Intro to `Fin n`" | `Fin` type | subtype reasoning | `fin_cases` | coercion `\uparrow` | TOO MUCH: split into (1) what `Fin` is, (2) `fin_cases` tactic, (3) coercion |
| "Intro to `Finset.sum`" | big operator concept | inductive sum reasoning | none new | `\sum x in s, f x` | BORDERLINE: new math + new notation OK if proof move is familiar |
| "Binomial theorem" | binomial theorem | multi-step induction + algebraic manipulation | `ring` (if new) | `Nat.choose` notation | TOO MUCH: must teach `Nat.choose` + Pascal's rule first |
| "Intro to `Finsupp`" | finsupp type | none new if finset is known | none new | `Finsupp.single` | OK: one new math item |
| "Matrix multiplication via `Finset.sum`" | matrix mul definition | double sum | none new | matrix notation | BORDERLINE: may need a "double sums" level first |

---

## 8. Recommended splits/merges

### Macro granularity: proposed world clusters

The course should be organized into approximately 5-6 macro modules:

**Module A: Finite index types (Fin)**
- World A1: What is `Fin n`?
- World A2: Computing with `Fin` (case analysis, exhaustion)
- World A3: (Pset) Transfer and retrieval on `Fin`

**Module B: Lists, multisets, and the hierarchy**
- World B1: Lists -- construction, membership, operations
- World B2: Multisets as quotients of lists
- World B3: From lists to multisets to finsets
- World B4: (Pset) Hierarchy transfer problems

**Module C: Finsets and their operations**
- World C1: Constructing finsets (empty, singleton, insert, cons)
- World C2: Membership and subset relations
- World C3: Union, intersection, difference
- World C4: Filter, image, map
- World C5: Cardinality -- counting elements
- World C6: (Pset) Finset reasoning under reduced scaffolding

**Module D: Fintype and counting**
- World D1: The `Fintype` type class and `Finset.univ`
- World D2: `Fintype.card` and cardinality of compound types
- World D3: Pigeonhole principle
- World D4: (Example world) Counting functions: `Fin n -> Fin m`
- World D5: (Pset) Counting and pigeonhole transfer

**Module E: Big operators**
- World E1: `Finset.sum` -- definition and basic lemmas
- World E2: Induction on `Finset.range` sums
- World E3: `Finset.prod` and multiplicative big operators
- World E4: Splitting, filtering, and reindexing sums
- World E5: (Example world) Classic sums: `1+2+...+n`, geometric series
- World E6: (Pset) Big-operator transfer problems

**Module F: Combinatorics and counting identities**
- World F1: Factorials and falling factorials
- World F2: Binomial coefficients and Pascal's rule
- World F3: Binomial identities (symmetry, row sum, Vandermonde)
- World F4: The binomial theorem
- World F5: (Example world) Pascal's triangle computations
- World F6: (Pset) Combinatorial identity transfer

**Module G: Advanced finite objects (capstone)**
- World G1: Finitely supported functions (`Finsupp`)
- World G2: Permutations of finite types
- World G3: Matrices as functions over finite index types
- World G4: (Boss world) Integration -- combining big operators, counting, and finite types

### Recommended splits:
- **Do not** merge `Fin` with `Finset`. They are conceptually distinct (index type vs collection type).
- **Do not** merge `List/Multiset` with `Finset`. The hierarchy deserves its own module.
- **Do** keep big operators separate from finset operations. Big operators are the payoff; finset operations are the infrastructure.

### Recommended merges:
- `Finset.cons` and `Finset.insert` can be taught in the same world; they are variations on the same idea.
- `sum` and `prod` basics could potentially share a world if the learner already knows `sum` well (since `prod` is the multiplicative analogue), but separate worlds are safer.

---

## 9. Recommended new levels or new worlds

### Example/case-study worlds (must be included):

1. **"The world of `Fin 3`"** (after Module A): Exhaustively enumerate elements, prove properties by cases, compute with `Fin.val`. This concretizes the `Fin` abstraction.

2. **"Building and inspecting `{1,2,3,4,5}`"** (after Module C): A case-study world where the learner builds a specific finset, checks membership, computes its power set, filters it, and counts elements. Pure concretization.

3. **"How many functions `Fin 2 -> Fin 3`?"** (in Module D): Count all functions from a 2-element type to a 3-element type. This concretizes `Fintype.card` for function types and connects to the multiplication principle.

4. **"Sum of the first n natural numbers"** (in Module E): A mini case-study world where the learner proves `\sum i in range n, i = n*(n-1)/2` by induction. The classic example of big-operator induction.

5. **"Pascal's triangle, row by row"** (in Module F): Compute specific rows of Pascal's triangle, verify identities on concrete numbers, and see the pattern before proving it generally.

### Critical levels that must exist:

- A level explicitly contrasting `List [1,2,1]` vs `Multiset [1,2,1]` vs `Finset {1,2}` to drive home the hierarchy (C3).
- A level where the learner encounters `DecidableEq` explicitly and understands why `Finset` needs it (C2).
- A level where `Finset.insert a s` when `a \in s` is a no-op, to prevent the misconception that insert always increases cardinality (C7).
- A level where `Finset.range 0` is empty, to calibrate the learner's range intuition (C9).
- A level proving the pigeonhole principle and a level applying it to a concrete problem (V16).
- A level using `Finset.induction_on` that is explicitly compared to `Nat.induction` (V4, L8).

---

## 10. Items that should be demoted, delayed, or hidden in the inventory

### Delay until needed:
- `Finsupp` (Module G): Do not introduce until big operators and finsets are stable.
- `Matrix` (Module G): Only as a capstone application. Do not frontload.
- `Equiv.Perm` (Module G): Requires both `Fintype` and `Equiv`; delay to capstone.
- `Finset.sigma`, `Finset.biUnion`: these are advanced operations; delay or omit.
- `Finset.sym`, `Finset.sym2`: combinatorial refinements; omit for basic course.

### Hide as aliases:
- `Finset.mem_coe`: the coercion from `Finset` to `Set` should be hidden early and revealed only when the learner needs it.
- `List.toFinset` vs `Multiset.toFinset`: teach one pipeline, hide variants until the hierarchy world.
- `rewrite` as alias for `rw`: support via `NewHiddenTactic`, do not clutter inventory.

### Demote to supporting:
- `Finset.disjUnion`: a niche optimization; demote from core to supporting.
- `Finset.erase`: less fundamental than `insert`/`filter`; introduce late.
- `Finset.attach`: advanced subtype manipulation; delay to Module D or later.
- `Multiset.powersetCard`: too specialized for the basic course.

---

## 11. Confidence notes

### High confidence:
- The MATH axis coverage is well-grounded in mathlib's actual API surface. `Fin`, `Finset`, `Fintype`, `List`, `Multiset`, `Finsupp`, big operators, `Nat.choose`, `Nat.factorial`, and `Matrix` are all mature, stable, well-documented areas of mathlib.
- The MOVE axis is derived from the actual proof patterns these theorems require. Finset induction, case exhaustion, membership rewriting, and big-operator splitting are the real proof moves.
- The LEAN axis tactics (`simp`, `ext`, `decide`, `fin_cases`, `omega`, `norm_num`) are standard and available.

### Medium confidence:
- The exact split between worlds in Modules E and F may need adjustment during authoring. The boundary between "big operators" and "counting identities" is somewhat fluid.
- The placement of `Matrix` content depends on how much linear-algebra flavor is appropriate for a basic course. It might be better as a brief capstone taste rather than a full module.
- `Finsupp` coverage depth: the basic API is clear, but deciding how deep to go (e.g., `Finsupp.sum`, `Finsupp.mapDomain`) depends on whether the course should preview later algebra courses.

### Low confidence:
- The exact novelty budget at the level granularity cannot be determined until specific level sequences are designed. The hotspot analysis above identifies the major risks, but individual levels may still accumulate too much novelty.
- Whether `List.permutations` (the function that enumerates all permutations of a list) is worth teaching depends on whether the course wants to include algorithmic/computational content. It might be better to focus on `Equiv.Perm` as the mathematical notion and skip the list-enumeration side entirely.
- The "double counting" transfer item (T6) is important for combinatorics but may be hard to teach well in a basic course without more algebraic infrastructure. It might be better suited to Course 32 (Combinatorics).

### Risk register:
1. **Type class overwhelm**: `Finset` operations require many type class assumptions (`DecidableEq`, `AddCommMonoid`, etc.). The course must teach these gradually, not dump them all at once.
2. **Coercion confusion**: Moving between `Fin n`, `Nat`, `Finset`, `Set`, and `Multiset` involves many coercions. Each coercion boundary should be an explicit teaching moment.
3. **`simp` over-reliance**: Many finset goals can be solved by `simp` with the right lemma set. The course must ensure learners understand the proof moves, not just the tactic.
4. **Scope creep into combinatorics**: The boundary between "counting identities" (in scope) and "combinatorics" (Course 32) must be maintained. Binomial coefficients and the pigeonhole principle are in scope; Hall's marriage theorem and Catalan numbers are not.

---

## Appendix: Proof-move decomposition for key theorem families

### Family 1: Finset membership and set operations
**Theorems**: `mem_union`, `mem_inter`, `mem_sdiff`, `mem_filter`, `mem_image`
**Proof moves needed**:
- Unfold membership via `simp` or `rw`
- Split conjunctions/disjunctions (`And.intro`, `Or.elim`)
- Introduce witnesses for `image` membership (`use`)
- Apply function to element

### Family 2: Cardinality arithmetic
**Theorems**: `card_union_add_card_inter`, `card_insert_of_not_mem`, `card_filter_le_card`
**Proof moves needed**:
- Case split on membership (`by_cases h : a \in s`)
- Rewrite with membership-conditional lemmas
- Natural number arithmetic (`omega`)
- Induction on finset (for general cardinality results)

### Family 3: Big-operator induction
**Theorems**: Sum of first n naturals, geometric sums, product telescoping
**Proof moves needed**:
- Induction on `n` with `sum_range_succ` to peel off last term
- Algebraic simplification in the inductive step (`ring`, `omega`)
- Rewriting the inductive hypothesis
- Splitting equalities via `calc`

### Family 4: Binomial coefficient identities
**Theorems**: Pascal's rule, symmetry, row sum, Vandermonde convolution
**Proof moves needed**:
- Recursion/induction using Pascal's rule
- Algebraic manipulation of factorials/choose values
- `norm_num` for base cases
- Sometimes: double-counting or bijection argument (advanced)

### Family 5: Pigeonhole and counting
**Theorems**: `Fintype.exists_ne_map_eq_of_card_lt`, injection/surjection cardinality bounds
**Proof moves needed**:
- Contradiction setup: assume injective, derive card inequality, contradict
- Witness extraction from a nonempty fiber
- Cardinality comparison via subset
- Case analysis on small types

### Family 6: Type-level counting
**Theorems**: `Fintype.card_fin`, `Fintype.card_prod`, `Fintype.card_fun`, `Fintype.card_sum`
**Proof moves needed**:
- Unfolding `Fintype.card` via `Finset.univ`
- Using `Fintype` instances (product, sum, function types)
- `simp` with `Fintype.card_*` lemma family
- Explicit enumeration for small types (`decide`, `fin_cases`)
