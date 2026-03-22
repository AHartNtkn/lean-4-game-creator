# Coverage Map: Finite Mathematics

Course scope: `Fin`, `Fintype`, `Finset`, finite sets as subtypes, lists vs multisets,
permutations, finitely supported functions, big operators, matrices over finite index types,
binomial coefficients, factorials, and counting identities.

Prerequisite: NNG4-level Lean fluency (`rw`, `exact`, `apply`, `intro`, `induction`, etc.).

---

## 1. Coverage Matrix Summary

### MATH axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| `Fin n` — the type with `n` elements | core | I S R G T | Foundation for everything |
| `Fin.val` and the subtype structure `{ i // i < n }` | core | I S R G | Must connect `Fin` to ℕ early |
| `Fin 0` (empty type) and `Fin 1` (unit type) | core | I S R W | Boundary cases teach structure |
| `Fin.castSucc`, `Fin.succ`, `Fin.last` | core | I S R G | Navigation within `Fin` |
| `Fin.cons`, `Fin.snoc` — tuple construction | core | I S R G | Building functions `Fin n → α` |
| `Finset α` — finite sets with decidable equality | core | I S R G T | Central data structure |
| `Finset.mem`, `Finset.subset` | core | I S R G | Basic membership/containment |
| `Finset.empty`, `Finset.singleton`, `Finset.insert` | core | I S R G | Constructors |
| `Finset.union`, `Finset.inter`, `Finset.sdiff` | core | I S R G T | Set operations |
| `Finset.filter` | core | I S R G | Predicate-based selection |
| `Finset.image`, `Finset.map` | core | I S R G | Forward images |
| `Finset.card` — cardinality | core | I S R G T | Counting |
| `Finset.range n` | core | I S R G | The finset `{0, ..., n-1}` |
| `Finset.powerset`, `Finset.powersetCard` | core | I S R G | Subsets and k-subsets |
| `Finset.product` — cartesian product | core | I S R G | Product constructions |
| `Finset.sigma` — dependent product | supporting | I S R | Dependent pairs over finsets |
| `Finset.diag`, `Finset.offDiag` | supporting | I S | Diagonal/off-diagonal pairs |
| `Finset.disjUnion` | supporting | I S R | Disjoint union (explicit proof) |
| `Fintype α` — typeclass for finite types | core | I S R G T | The finiteness abstraction |
| `Fintype.card α` | core | I S R G T | Cardinality of a type |
| `Fintype.elems` / `Finset.univ` | core | I S R G | The universal finset |
| `Fintype` instances: `Fin n`, `Bool`, `Unit`, products, sums, subtypes | core | I S R G | How finiteness composes |
| `Fintype.card_fin`, `Fintype.card_prod`, `Fintype.card_sum` | core | I S R G T | Counting type constructions |
| `Fintype.card_fun` / `Fintype.card_pi` | supporting | I S R | Counting functions |
| `Multiset α` — lists up to permutation | core | I S R G | Intermediate abstraction |
| `Multiset.card`, `Multiset.count` | core | I S R | Size and multiplicity |
| `Multiset` vs `Finset` — the `nodup` distinction | core | I S W T | Why both exist |
| `List α` — ordered sequences | core | I S R G | Foundation for Multiset |
| `List.length`, `List.mem`, `List.append`, `List.reverse` | core | I S R | Basic list operations |
| `List.map`, `List.filter`, `List.foldl`/`List.foldr` | core | I S R G | Higher-order list operations |
| `List.Perm` — permutation relation on lists | core | I S R G T | Connects lists to multisets |
| `List.Nodup` | core | I S R | Connects lists to finsets |
| `Finsupp α β` — finitely supported functions | supporting | I S R G | Functions vanishing a.e. |
| `Finsupp.support`, `Finsupp.single`, `Finsupp.mapDomain` | supporting | I S R | Key Finsupp operations |
| `Finset.sum`, `Finset.prod` — big operators | core | I S R G T | Summation/product over finsets |
| `Finset.sum_empty`, `Finset.sum_singleton`, `Finset.sum_insert` | core | I S R G | Constructor lemmas for sums |
| `Finset.sum_union` (disjoint), `Finset.sum_filter` | core | I S R G | Decomposition lemmas |
| `Finset.sum_congr`, `Finset.prod_congr` | core | I S R G | Rewriting under big operators |
| `Finset.sum_const`, `Finset.prod_const` | core | I S R | Constant-function sums/products |
| `Finset.sum_add_distrib`, `Finset.prod_mul_distrib` | core | I S R G | Algebraic distributivity |
| `Finset.sum_image`, `Finset.prod_image` | supporting | I S R | Reindexing |
| `Finset.sum_fiberwise` / `Finset.prod_fiberwise` | supporting | I S | Grouping by fibers |
| `∑ᶠ` / `∏ᶠ` — `finsum` / `finprod` | optional | I S | Alternative notation |
| `Nat.factorial` | core | I S R G | n! |
| `Nat.ascFactorial`, `Nat.descFactorial` | supporting | I S | Rising/falling factorials |
| `Nat.choose` — binomial coefficients | core | I S R G T | C(n,k) |
| `Nat.choose_succ_succ` — Pascal's identity | core | I S R G | Recursive structure |
| `Nat.choose_symm` | core | I S R | Symmetry C(n,k) = C(n,n-k) |
| `Nat.choose_eq_factorial_div_factorial` | core | I S R | Factorial formula |
| `Nat.multichoose` — stars and bars | supporting | I S | Multiset counting |
| `Finset.card_powerset`, `Finset.card_powersetCard` | core | I S R G T | 2^n and C(n,k) via sets |
| `add_pow` — binomial theorem | core | I S R G T | (x+y)^n expansion |
| `Nat.sum_range_choose` — sum of binomial row = 2^n | core | I S R | Row-sum identity |
| Inclusion-exclusion: `Finset.card_union_add_card_inter` | core | I S R G T | Fundamental counting |
| `Matrix m n α` — functions `m → n → α` | supporting | I S R | Matrices as functions |
| `Matrix.diagonal`, `Matrix.diag`, `Matrix.transpose` | supporting | I S | Basic matrix operations |
| `Finset.Nat.antidiagonal` | supporting | I S | Pairs summing to n |
| `Finset.sort` / `Finset.orderIsoOfFin` | optional | I S | Linearization of finsets |
| `Finset.fold` | optional | I | Low-level fold |
| `Fintype.piFinset` | supporting | I S | Finset of functions |

### MOVE axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| Unfold a definition to expose structure | core | I S R G T | `unfold`, `simp only [...]`, `change` |
| Case split on `Fin` elements (`fin_cases`-style reasoning) | core | I S R G | Enumerate all cases for small `n` |
| Induction on `Fin n` / on `n : ℕ` for `Fin`-indexed objects | core | I S R G T | Recursive proofs |
| Prove set equality by mutual containment (`ext`) | core | I S R G T | `⊆` + `⊇` |
| Prove membership by construction | core | I S R G | Show `x ∈ s` concretely |
| Prove non-membership / disjointness | core | I S R G | `x ∉ s` by contradiction or `Disjoint` |
| Rewrite under a binder (inside `∑`, `∏`, `∀`, `∃`) | core | I S R G | `Finset.sum_congr rfl (fun x hx => ...)` |
| Split a sum/product by partition | core | I S R G | `sum_union`, `sum_filter`, `sum_fiberwise` |
| Telescoping / cancellation in sums | supporting | I S R | Adjacent-term patterns |
| Double counting / bijective proof | core | I S R G T | Same quantity two ways |
| Cardinality argument via injection/surjection | core | I S R G T | `card_le_of_injective`, `card_le_of_surjective` |
| Prove equality by showing ≤ in both directions | supporting | I S R | Antisymmetry for ℕ |
| Choose an element from a nonempty finset | core | I S R G | `Finset.Nonempty` → witness |
| Pigeonhole argument | supporting | I S R | `card_lt_card` + injection failure |
| Induction on `Finset.card` | supporting | I S R | Structural induction on set size |
| Induction with `Finset.cons` / `Finset.insert` | core | I S R G | Building up finsets one element at a time |
| Prove a big-operator identity by induction | core | I S R G T | Canonical proof shape for sums |
| Appeal to decidability for membership | supporting | I S W | `Decidable` instances |
| Use `Equiv` to transfer cardinality | supporting | I S R | `Fintype.card_congr` |

### LEAN axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| `simp` with Finset lemmas | core | I S R G | `simp [Finset.mem_insert, ...]` |
| `omega` for `Fin`/ℕ arithmetic | core | I S R G | Closes arithmetic goals |
| `decide` for small finite goals | core | I S R | NNG4 baseline, but new contexts |
| `ext` for set/function extensionality | core | I S R G | Prove `s = t` or `f = g` |
| `congr` / `gcongr` for structural matching | supporting | I S R | Match structure of goals |
| `constructor` for `∧` and `↔` | core | I S R G | NNG4 baseline, new contexts |
| `use` for existential witnesses | core | I S R G | Provide ∃ witnesses |
| `obtain` for destructuring | core | I S R G | Break apart ∧, ∃, ↔ |
| `norm_num` for numeric goals | core | I S R G | Simplify concrete numbers |
| `ring` / `ring_nf` for algebraic manipulation | supporting | I S R | Algebraic simplification |
| `calc` blocks for chains of equalities | core | I S R G T | Multi-step rewrites |
| `conv` for targeted rewriting | supporting | I S | Rewrite inside nested structures |
| `rcases` / `rintro` with patterns | supporting | I S R | Destructuring introduction |
| `have` for intermediate lemmas | core | I S R G | NNG4 baseline, used constantly |
| `suffices` for backward reasoning | supporting | I S R | Prove a weaker claim first |
| `push_neg` for negation manipulation | supporting | I S | ¬∀ ↔ ∃¬ etc. |
| `contradiction` | supporting | I S R | Close absurd goals |
| `by_contra` | supporting | I S R | Proof by contradiction |
| `refine` for partial term construction | supporting | I S R | Fill in `?_` holes |
| `fin_cases` (when allowed) | supporting | I S | Enumerate `Fin n` elements |

### NOTATION axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| `Fin n` vs `{ i : ℕ // i < n }` — the same type, two faces | core | I S W T | Central notation issue |
| `↑i` (coercion `Fin n → ℕ`) vs `i.val` | core | I S R W | Coercion syntax |
| `⟨k, hk⟩` constructor for `Fin n` | core | I S R | Anonymous constructor |
| `∈` for `Finset` membership | core | I S R G | Standard notation |
| `⊆` for `Finset.Subset` | core | I S R G | Standard notation |
| `∪`, `∩`, `\` for Finset operations | core | I S R G W | These are lattice `⊔`/`⊓`/`\` underneath |
| `{a, b, c}` literal finset notation | core | I S R | `{a, b, c} = insert a (insert b {c})` |
| `∑ x ∈ s, f x` and `∑ x : Fin n, f x` | core | I S R G | Big-operator notation |
| `∏ x ∈ s, f x` and `∏ x : Fin n, f x` | core | I S R G | Big-operator notation |
| `#s` for `Finset.card s` (in `Finset` locale) | supporting | I S | Optional shorthand |
| `s ×ˢ t` for `Finset.product` | supporting | I S R | Product notation |
| `Finset.range n` — `{0, ..., n-1}` not `{1, ..., n}` | core | I S W | Off-by-one confusion |
| `n.choose k` vs `Nat.choose n k` | supporting | I S | Dot notation |
| `n !` / `Nat.factorial n` | supporting | I S | Factorial notation |
| `↑s` coercion `Finset α → Set α` | supporting | I S W | Finset-to-Set lift |
| `Fin n → α` as "tuple" or "vector" | core | I S T | Functions as data |
| Anonymous constructor `⟨..., ...⟩` for subtypes | core | I S R | Pervasive |

### MISCONCEPTION axis

| Item | Importance | Notes |
|------|-----------|-------|
| `Fin n` elements start at 0, not 1 | core | Constant source of off-by-one errors |
| `Finset.range n` is `{0, ..., n-1}`, not `{0, ..., n}` | core | Another off-by-one |
| `Finset` requires `DecidableEq` — not every type works | core | Learners will try `Finset` on undecidable types |
| `Finset` operations are lattice operations — `∪` is `⊔`, `∩` is `⊓` | core | Finset.union_comm is also sup_comm; aliases bypass `DisabledTheorem` |
| `Multiset` is NOT `Finset` — duplicates are retained | core | Confusion between multisets and sets |
| `List` is NOT `Multiset` — order matters | core | Must distinguish all three |
| Big operator over empty set is identity (0 for sum, 1 for prod) | core | Learners forget the base case |
| `Finset.insert` does nothing if element already present | supporting | Idempotence is surprising |
| `Finset.image` can shrink cardinality (non-injective maps) | core | `card_image_le` vs `card_image_of_injOn` |
| `Nat.choose n k = 0` when `k > n` | core | Surprising to learners |
| `Fin.val` is injective but the coercion can hide the proof obligation | supporting | Coercion confusion |
| `Finset.sum` requires `AddCommMonoid`, not just `Add` | supporting | Typeclass constraints |
| `Matrix m n α` is just `m → n → α` — no special magic | supporting | Demystify matrices |

### TRANSFER axis

| Item | Importance | Notes |
|------|-----------|-------|
| "A finite set is determined by its membership predicate" — ext principle | core | Carries to all of mathematics |
| "Count by bijection: same size means same count" | core | Fundamental combinatorial reasoning |
| "Split a sum into parts, compute each part, add" — partition reasoning | core | Universal proof strategy |
| "Prove a formula by induction on the number of elements" | core | Inductive counting |
| "If f is injective, |image| = |domain|; if not, |image| < |domain|" | core | Injection/surjection intuition |
| "Pascal's triangle encodes subset counting" | core | Classical combinatorial insight |
| "Double counting: compute the same quantity two different ways" | core | Powerful counting technique |
| "The pigeonhole principle: too many pigeons, not enough holes" | supporting | Foundational discrete reasoning |
| "A list is ordered; a multiset forgets order; a set forgets order and multiplicity" | core | The abstraction ladder |

### EXAMPLE axis

| Item | Role | Notes |
|------|------|-------|
| `Fin 0` | counterexample / boundary | Empty type — no elements, everything vacuously true |
| `Fin 1` | concretization | Unique/Unit — exactly one element |
| `Fin 2` | concretization | Isomorphic to `Bool` — two elements, good for exhaustive case splits |
| `Fin 3`, `Fin 4` | concretization | Small enough to enumerate, large enough to need structure |
| `Finset.range 5` | concretization | Concrete finset `{0,1,2,3,4}` for computation |
| `{1, 2, 3} : Finset ℕ` | concretization | Literal finset for membership/operations |
| `Finset.powerset {1,2,3}` | concretization | 8 subsets — connects to 2^n |
| `Finset.powersetCard 2 {1,2,3}` | concretization | 3 two-element subsets — connects to C(3,2) |
| `Finset.range n` for `∑ i in range n, f i` | concretization | Summation over ranges |
| `Fin 2 → ℕ` as ordered pairs | concretization / integration | Functions as tuples |
| `Fin n → Fin m` — counting functions | integration | `Fintype.card_fun` = m^n |
| `Fin n ↪ Fin m` — counting injections | integration | Connects to descFactorial |
| `[1, 2, 3, 2]` vs `{1, 2, 3, 2}` as `Multiset` vs `Finset` | counterexample | Shows multiset ≠ finset |
| `[1, 2, 3]` vs `[3, 1, 2]` — same multiset, different lists | counterexample | Shows list ≠ multiset |
| Empty list `[]`, empty multiset `0`, empty finset `∅` | boundary | Three faces of emptiness |
| `Matrix (Fin 2) (Fin 2) ℤ` | concretization | 2×2 integer matrices |
| `Nat.choose 5 2 = 10` | concretization | Concrete binomial computation |
| `Nat.factorial 5 = 120` | concretization | Concrete factorial computation |
| `Finset.Nat.antidiagonal 3` | concretization | `{(0,3),(1,2),(2,1),(3,0)}` |
| `Finsupp.single` on `ℕ → ℕ` | concretization | A function that is 0 almost everywhere |

---

## 2. Core Items That Must Not Be Missed

These items are non-negotiable. If any is omitted or only introduced without practice, the course fails.

1. **`Fin n`** — what it is, how to construct elements, how `val` relates to ℕ, successor/castSucc navigation, boundary cases `Fin 0` and `Fin 1`.

2. **`Finset`** — membership, subset, empty/singleton/insert, union/inter/sdiff, filter, image, card. This is the central object of the course.

3. **`Fintype`** — the typeclass, `Finset.univ`, `Fintype.card`, how finiteness composes (products, sums, subtypes, function types).

4. **`Finset.card`** and cardinality arguments — `card_mono`, `card_lt_card`, `card_union_add_card_inter`, `card_image_of_injOn`, `card_image_le`, `card_powerset`, `card_powersetCard`, `card_product`.

5. **Big operators** — `Finset.sum` and `Finset.prod`, the constructor lemmas (`sum_empty`, `sum_insert`, `sum_singleton`), decomposition (`sum_union`, `sum_filter`), congruence, `sum_const`, distributivity.

6. **Binomial coefficients** — `Nat.choose`, Pascal's identity, symmetry, factorial formula, connection to `Finset.powersetCard`, the binomial theorem (`add_pow`), `sum_range_choose`.

7. **Induction over finsets** — `Finset.cons`/`Finset.insert` induction for proving big-operator identities and cardinality results.

8. **The List → Multiset → Finset abstraction ladder** — what each level forgets, how they relate, when to use which.

9. **Proof by ext(ensionality)** — for finsets and for functions `Fin n → α`.

10. **Double counting / bijective proof** — the fundamental combinatorial proof strategy.

---

## 3. Example Plan

### Definitions needing concrete examples

| Definition | Examples to use | Counterexamples | Variety needed |
|-----------|----------------|-----------------|---------------|
| `Fin n` | `Fin 0` (empty), `Fin 1` (unit), `Fin 2` (Bool), `Fin 5` (small concrete) | — | Range from n=0 to n=5+ |
| `Finset` | `{1,2,3}`, `∅`, `Finset.range 5`, `Finset.univ : Finset (Fin 3)` | — | Literal, range, and univ constructions |
| `Finset.card` | `#{1,2,3} = 3`, `#∅ = 0`, `#(Finset.range n) = n` | `#(Finset.image f s)` when f not injective | Injection/non-injection contrast |
| `Finset.powerset` | `powerset {1,2}` — enumerate all 4 subsets | — | Small enough to see all subsets |
| `Finset.powersetCard` | `powersetCard 2 {1,2,3}` = `{{1,2},{1,3},{2,3}}` | `powersetCard 4 {1,2,3}` = `∅` | Over-sized k gives empty |
| `Multiset` | `{1,2,2,3}` — count of 2 is 2 | `{1,2,3}` as finset loses the second 2 | Contrast multiset vs finset |
| `List` | `[1,2,3]` and `[3,1,2]` — different lists, same multiset | `[1,2,3]` ≠ `[3,1,2]` as lists | Order matters |
| `List.Perm` | `[1,2,3] ~ [3,1,2]` — a permutation | `[1,2,3]` not perm of `[1,2,2]` | Same vs different multiplicities |
| `List.Nodup` | `[1,2,3]` has nodup | `[1,2,2,3]` does not | Clean vs duplicated |
| `Fintype` | `Fintype (Fin n)`, `Fintype Bool`, `Fintype (Fin 2 × Fin 3)` | `ℕ` is not a `Fintype` | Finite vs infinite |
| `Nat.choose` | `choose 5 2 = 10`, `choose 4 0 = 1`, `choose 4 4 = 1` | `choose 3 5 = 0` | Boundary cases (k=0, k=n, k>n) |
| `Nat.factorial` | `factorial 5 = 120`, `factorial 0 = 1` | — | Base case 0! = 1 is surprising |
| `Finset.sum` | `∑ i in range 4, i = 6`, `∑ i in {1,2,3}, i^2 = 14` | Sum over ∅ = 0 | Concrete arithmetic, empty base case |
| `Finset.prod` | `∏ i in range 4, (i+1) = 24 = 4!` | Product over ∅ = 1 | Connects to factorial |
| `Matrix` | `!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ` | — | Small concrete matrix |
| `Finsupp` | `Finsupp.single 3 7 : ℕ →₀ ℤ` — nonzero only at 3 | — | Point function |
| `Finset.product` | `{1,2} ×ˢ {3,4}` = `{(1,3),(1,4),(2,3),(2,4)}` | — | Enumerate all pairs |
| `add_pow` (binomial thm) | `(x+y)^3 = x^3 + 3x^2y + 3xy^2 + y^3` | — | Small concrete expansion |

### Definitions needing counterexamples

| Definition/property | Counterexample | What it teaches |
|--------------------|---------------|----------------|
| `Finset.image` preserves card | `image (fun _ => 0) {1,2,3}` has card 1, not 3 | Injectivity matters |
| `Fintype` | `ℕ` has no `Fintype` instance | Not every type is finite |
| `List.Nodup` | `[1,2,2]` has duplicates | Nodup is a property, not automatic |
| `Multiset = Finset` | `{1,2,2} : Multiset ℕ` has card 3, not 2 | Duplicates matter in multisets |
| `Nat.choose n k` when k > n | `choose 3 5 = 0` | Boundary behavior |
| `Finset.insert` idempotence | `insert 1 {1,2} = {1,2}` — no change | Already-present elements |

---

## 4. Proof-Move Clusters

### Cluster A: Membership and containment
**Moves**: prove `x ∈ s`, prove `s ⊆ t`, prove `s = t` by `ext`, prove `x ∉ s`
**Why together**: These are the basic language for talking about finsets. Every later cluster assumes fluency here.
**Theorem families**: `mem_insert`, `mem_union`, `mem_inter`, `mem_filter`, `mem_image`, `mem_range`, `mem_powerset`, `subset_iff`

### Cluster B: Cardinality arithmetic
**Moves**: compute `card` of concrete finsets, use `card_insert_of_notMem`, `card_union_add_card_inter`, `card_sdiff`, `card_product`, `card_image_of_injOn`
**Why together**: Cardinality is the bridge between finsets and numbers. These moves all produce ℕ-valued equations.
**Theorem families**: all `card_*` lemmas

### Cluster C: Induction on finsets
**Moves**: induction via `Finset.cons`/`Finset.insert`, prove base case for `∅`, prove inductive step with `h : a ∉ s`
**Why together**: This is the dominant proof shape for big-operator identities and many cardinality results.
**Theorem families**: `Finset.induction_on` (note: `Finset.cons_induction` removed — minor variant with same proof strategy, not worth a separate level)

### Cluster D: Big-operator manipulation
**Moves**: unfold `sum`/`prod` on small finsets, use `sum_insert`, `sum_union` (disjoint), `sum_congr`, `sum_add_distrib`, `sum_const`, `sum_filter`
**Why together**: These are the algebraic moves for working with `∑` and `∏`.
**Theorem families**: `Finset.sum_*`, `Finset.prod_*`

### Cluster E: Combinatorial identities via big operators
**Moves**: prove `∑ k in range (n+1), choose n k = 2^n`, binomial theorem, Vandermonde-style, double counting
**Why together**: These combine induction (Cluster C) with big-operator algebra (Cluster D) and binomial coefficient facts.
**Theorem families**: `add_pow`, `Nat.sum_range_choose`, Pascal's identity, `card_powersetCard`

### Cluster F: Fin navigation and case analysis
**Moves**: construct elements of `Fin n`, use `Fin.val` / coercion, case split on `Fin n` for small `n`, use `Fin.succ`/`Fin.castSucc`/`Fin.last`
**Why together**: Working with `Fin` requires its own small vocabulary of moves.
**Theorem families**: `Fin.val_*`, `Fin.mk_*`, `Fin.ext_iff`

### Cluster G: Tuple construction and manipulation
**Moves**: build `Fin n → α` via `Fin.cons`/`Fin.snoc`, decompose via `Fin.tail`/`Fin.init`, use `Fin.append`
**Why together**: Functions out of `Fin n` are "vectors" and have their own construction/destruction patterns.
**Theorem families**: `Fin.cons_*`, `Fin.snoc_*`, `Fin.tail_*`

### Cluster H: The List → Multiset → Finset pipeline
**Moves**: convert between layers, understand what each quotient forgets, use `List.Perm`, use `List.Nodup`
**Why together**: Understanding this pipeline is essential for understanding why `Finset` works the way it does.
**Theorem families**: `Multiset.coe_*`, `Finset.val`, `List.toFinset_*`

### Cluster I: Equivalences and cardinality transfer
**Moves**: build an `Equiv` between finite types, conclude `Fintype.card` equality via `card_congr`, use `card_fin`, `card_prod`, `card_sum`
**Why together**: Bijective proofs are a major proof strategy in combinatorics.
**Theorem families**: `Fintype.card_congr`, `Fintype.card_*`

---

## 5. Novelty Hotspots

These are places where too much novelty concentrates if not carefully sequenced.

### Hotspot 1: First encounter with `Finset`
- New MATH: `Finset`, membership, subset
- New NOTATION: `∈`, `⊆`, `∪`, `∩`, `{a, b, c}` literals, `∅`
- New LEAN: `simp [Finset.mem_insert, ...]`, `ext`, `decide` for small goals
- **Risk**: Learner faces new data structure + new notation + new simp lemmas simultaneously
- **Mitigation**: Introduce `Finset` membership first on tiny literal finsets where `decide` works. Add notation one piece at a time.

### Hotspot 2: Big operators introduction
- New MATH: `Finset.sum`, `Finset.prod`
- New NOTATION: `∑ x ∈ s, f x`, binder syntax
- New MOVE: rewriting under binders, sum decomposition
- New LEAN: `sum_congr`, `sum_insert`, interaction with `simp`
- **Risk**: Big-operator notation + binder syntax + new proof moves all at once
- **Mitigation**: Start with `∑ x ∈ {a, b}, f x` where the sum unfolds to two terms. Build notation familiarity before proof moves.

### Hotspot 3: Finset induction
- New MOVE: induction on finsets (different from ℕ induction)
- New LEAN: `Finset.induction_on`
- **Risk**: The induction hypothesis shape is unfamiliar (involves `a ∉ s`)
- **Mitigation**: Precede with a level that shows the `insert` constructor explicitly. Let learner see the structure before doing induction.

### Hotspot 4: Binomial coefficient identities
- New MATH: `Nat.choose`, Pascal's identity, binomial theorem
- New MOVE: induction + big-operator manipulation combined
- **Risk**: The proofs require both Cluster C and Cluster D moves simultaneously
- **Mitigation**: Ensure both clusters are practiced individually before combining.

### Hotspot 5: `Fin` vs ℕ coercion
- New NOTATION: `↑i` vs `i.val` vs `i`
- New LEAN: coercion behavior, `omega` on `Fin` goals
- **Risk**: Coercion confusion is pervasive and hard to diagnose from error messages
- **Mitigation**: Dedicate explicit levels to the coercion story. Show what `↑` does and when it appears.

### Hotspot 6: Multiset/List/Finset distinctions
- New MATH: three related but different types
- New MISCONCEPTION: confusing which operations are available where
- **Risk**: Three similar-looking types with different APIs
- **Mitigation**: Present the abstraction ladder explicitly. Use concrete counterexamples showing what each level forgets.

---

## 6. Items to Demote, Delay, or Hide

### Delay (introduce late, after core is solid)

| Item | Reason |
|------|--------|
| `Finsupp` | Requires comfort with zero-default functions; not needed for core counting |
| `Matrix` | Is just `m → n → α`; introduce after `Fin n → α` tuple story is solid |
| `finsum`/`finprod` | Alternative notation; confusing if presented alongside `Finset.sum` |
| `Finset.sigma` | Dependent products are harder than simple products |
| `Nat.ascFactorial`, `Nat.descFactorial` | Supporting material; introduce only when needed for a specific identity |
| `Nat.multichoose` | Stars-and-bars is a secondary topic |
| `Finset.Nat.antidiagonal` | Useful but specialized |
| `Finset.sort`, `Finset.orderIsoOfFin` | Ordering finsets is tangential to core counting |
| `Finset.fold` | Low-level mechanism; `Finset.sum`/`Finset.prod` are the user-facing API |

### Hide (make available but don't teach explicitly)

| Item | Reason |
|------|--------|
| `Finset.disjUnion` | `Finset.union` + disjointness proof is clearer pedagogically |
| `Finset.choose` / `Multiset.choose` | Specialized selection; `obtain` + membership is more transferable |
| `Finset.fold` | Internal mechanism, not learner-facing |
| Lattice aliases for Finset ops (`sup_comm`, `inf_le_left`, etc.) | **Must be disabled** — these are exploit vectors, not teaching material |
| `fin_cases` | Disable in early levels to force manual case analysis; enable later |
| `interval_cases` | Similar to `fin_cases`; disable when manual reasoning is the point |

### Gate (disable per-level to force specific proof moves)

| Item | When to disable | Why |
|------|----------------|-----|
| `norm_num` | When manual computation is the lesson | Prevents thinking about why `choose 5 2 = 10` |
| `decide` | When proof structure matters | One-shots many small finite goals |
| `simp` (already baseline disabled) | Always disabled at baseline | Too powerful on Finset lemmas |
| `fin_cases` | When manual `Fin` case analysis is the lesson | Automates the very thing being taught |
| `ext` | When the learner should discover that extensionality is the right move | Don't gate forever; gate the intro level |
| Lattice lemmas (`sup_comm`, `inf_comm`, etc.) | Always when Finset ∪/∩ are the topic | Lattice aliases bypass intended Finset reasoning |

---

## 7. Confidence Notes

### High confidence

- **Core Finset API**: The mathlib4 API for `Finset` is stable and well-documented. The `mem_*`, `card_*`, `sum_*`, `prod_*` lemma families are reliable building blocks.
- **Fin API**: `Fin n` is well-supported with `val`, `mk`, arithmetic, `cons`/`snoc`, and the tuple story is clean.
- **Binomial coefficients**: `Nat.choose`, Pascal's identity, symmetry, factorial formula, and `add_pow` are all verified present in current mathlib4.
- **Big operators**: `Finset.sum` and `Finset.prod` have extensive lemma libraries that support the proof-move clusters outlined.
- **Lattice alias exploit**: Confirmed — Finset ∪/∩ are lattice ⊔/⊓, and aliases like `sup_comm`, `inf_le_left` must be disabled alongside Finset-specific lemmas.

### Needs architect judgment

- **World boundaries**: I've identified 9 proof-move clusters and ~6 novelty hotspots. The right world count is somewhere between 8 and 14. The architect must decide where cluster boundaries become world boundaries and where clusters can share a world.
- **Finsupp depth**: The course description includes "finitely supported functions" but it's unclear how deep to go. A minimal treatment (definition + `single` + `support`) vs a thorough treatment (including `mapDomain`, `curry`, `sum`) changes the course length significantly. I'd recommend minimal for a first course.
- **Matrix depth**: Similarly, "matrices over finite index types" could mean "show that `Matrix (Fin n) (Fin n) α` is just a function" (1-2 levels) or "do matrix arithmetic" (a full world). The former seems right for this course; the latter belongs in a linear algebra course.
- **List/Multiset depth**: Lists and multisets are important for understanding *why* Finset works the way it does. But the course could spend 1 world or 3 worlds here. I'd recommend 1.5 — enough to build intuition for the abstraction ladder, not enough to become a list-algorithms course.
- **Counting identities scope**: The course description says "counting identities that underlie later combinatorics." This could range from just Pascal + binomial theorem to Vandermonde, hockey stick, Zhu Shijie, alternating sums, etc. The architect should decide how many identity levels the final world(s) should have.
- **`Fintype.card_fun` / `Fintype.card_pi`**: These are `m^n` and `∏ card (β i)`. Powerful counting results, but the proofs in mathlib use non-trivial machinery. The architect should decide whether to include them as black-box counting tools or try to build toward them.
- **Pigeonhole placement**: Pigeonhole is a natural capstone for cardinality reasoning. It could be a boss level for the cardinality world or the start of an integration/applications world. The architect should decide.
