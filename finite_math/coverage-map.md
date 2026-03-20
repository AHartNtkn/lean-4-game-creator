# Finite Mathematics — Coverage Map

## Course scope (from long_term.md)

`Fin`, `Fintype`, `Finset`, finite sets as subtypes, lists versus multisets,
permutations of lists, finitely supported functions, finite products of finsets,
matrices over finite index types, big operators, binomial coefficients,
factorials, finite sums/products, and counting identities.

**Out of scope:** graph theory, Ramsey theory, additive combinatorics.

**Prerequisites:** NNG4-level Lean fluency. No serious prior mathematics.

---

## 1. Coverage matrix summary

### MATH axis

| Item | Importance | I | S | R | G | T | W | Notes |
|------|-----------|---|---|---|---|---|---|-------|
| `Fin n` (type, val, isLt) | core | W1 | W1,W2 | W7,W11 | W13,W16 | W17 | W1 | Foundation for everything indexed |
| `Fin.last`, `Fin.zero` | core | W1 | W1 | W2 | W11 | | | |
| `Fin.succ`, `Fin.castSucc`, `Fin.cast` | core | W2 | W2 | W11,W13 | W13 | | W2 | cast confusion is real |
| Fin arithmetic (add, mod) | supporting | W2 | W2 | | W15 | | W2 | Modular wrap surprises |
| Fin tuples (`cons`, `snoc`, `init`, `tail`) | supporting | W2 | W2 | W13 | W16 | | | |
| `List α` (cons, append, length, mem) | core | W3 | W3 | W4 | W15 | | | |
| `List.map`, `List.filter` | core | W3 | W3 | W5 | | | | |
| `List.Perm` | supporting | W3 | W3,W15 | W15 | W15 | | W3 | Order doesn't matter — motivates Multiset |
| `List.Nodup` | supporting | W3 | W3 | W4 | | | W3 | Bridge to Finset |
| `Multiset α` | core | W4 | W4 | W5 | | | W4 | |
| `Multiset.toFinset`, `List.toFinset` | core | W4 | W4,W5 | W5 | | | W4 | Duplicates are dropped |
| `Finset α` (type, membership) | core | W5 | W5,W6 | W7-W17 | everywhere | W10,W17 | W5 | Central type of course |
| `∅`, `{a}`, `insert` for Finset | core | W5 | W5 | W6 | W8,W11 | | W5 | |
| `Finset.range n` | core | W5 | W5,W11 | W9,W11 | W11,W17 | W13 | | |
| `Finset.cons` | supporting | W5 | W5 | W11 | | | W5 | Requires proof of non-membership |
| `Finset.union` (∪) | core | W6 | W6 | W8 | W8,W11 | W10 | W6 | Lattice aliases! |
| `Finset.inter` (∩) | core | W6 | W6 | W8 | W8 | W10 | W6 | Lattice aliases! |
| `Finset.sdiff` (\) | core | W6 | W6 | W8 | W8 | | | |
| `Finset.filter` | core | W6 | W6,W8 | W11 | W11,W13 | W17 | | |
| `Finset.Subset` (⊆) | core | W6 | W6 | W8 | W8 | | W6 | Lattice ≤ alias |
| `Disjoint` for Finset | core | W6 | W6 | W8,W11 | W11 | | W6 | |
| `Finset.image` | core | W7 | W7 | W8 | W11,W13 | | W7 | Non-injective → duplicates lost |
| `Finset.map` (with embedding) | supporting | W7 | W7 | | W13 | | W7 | Requires embedding, preserves card |
| `Finset.product` (×ˢ) | core | W7 | W7 | W10 | W13,W17 | | | |
| `Finset.sigma` | supporting | W7 | W7 | W13 | W13 | | | |
| `Fintype` class | core | W8 | W8 | W11 | W13,W16 | | | |
| `Finset.univ` | core | W8 | W8,W11 | W13 | W13,W16 | | | |
| `Fintype.card` | core | W8 | W8 | W9,W10 | W10,W17 | | | |
| `Finset.card` | core | W9 | W9 | W10 | W10,W17 | W17 | | |
| `card_union_add_card_inter` | core | W9 | W9 | W10 | W17 | | | Inclusion-exclusion |
| `card_image_of_injective` | core | W9 | W9 | | W10 | | W9 | Injectivity required |
| Pigeonhole principle | core | W9 | W9 | W10 | W17 | W10 | | |
| `Nat.factorial` | core | W10 | W10 | W15,W17 | W17 | | | |
| `Nat.choose` (Pascal's recurrence) | core | W10 | W10 | W12 | W17 | | | |
| `Nat.choose_eq_factorial_div_factorial` | core | W10 | W10 | | W17 | | | |
| `Nat.choose_symm` | core | W10 | W10 | W12 | W17 | | | |
| `Nat.ascFactorial`, `Nat.descFactorial` | supporting | W10 | W10 | | W17 | | | |
| `Nat.multichoose` | supporting | W10 | W10 | | W17 | | | Stars and bars |
| `Finset.powerset` | core | W12 | W12 | W17 | W17 | | | |
| `Finset.powersetCard` | core | W12 | W12 | | W17 | | | |
| `card_powerset` = 2^n | core | W12 | W12 | | W17 | | | |
| `card_powersetCard` = choose | core | W12 | W12 | | W17 | | | |
| `Finset.sum` (∑) | core | W11 | W11,W13 | W13,W17 | W16,W17 | W17 | | |
| `Finset.prod` (∏) | core | W11 | W11,W13 | W13,W17 | W16,W17 | W17 | | |
| `sum_empty`, `sum_singleton`, `sum_insert` | core | W11 | W11 | W13 | W13,W17 | | | |
| `sum_union` (disjoint) | core | W11 | W11 | W13 | W17 | | | |
| `sum_filter` / `sum_ite` | core | W11 | W11,W13 | W13 | W17 | | | |
| `sum_const`, `sum_range` | core | W11 | W11 | W13 | W17 | | | |
| `prod_range_succ` | core | W11 | W11,W13 | | W17 | | | |
| `map_sum`, `map_prod` | supporting | W13 | W13 | | W17 | | | Homomorphism compatibility |
| `sum_bij` / `prod_bij` | supporting | W13 | W13 | W17 | W17 | | | Bijective reindexing |
| `sum_comm` / `prod_comm` | supporting | W13 | W13 | | W17 | | | Swapping summation order |
| `sum_sigma` / `prod_sigma` | supporting | W13 | W13 | | W17 | | | Iterated sums/products |
| `Fin.sum_univ_succ` / `Fin.prod_univ_succ` | core | W13 | W13 | W17 | W17 | | | Peeling off first/last |
| `Finsupp` (α →₀ M) | supporting | W14 | W14 | | W14 | | | |
| `Finsupp.support` | supporting | W14 | W14 | | W14 | | | |
| `Finsupp.single`, `Finsupp.mapRange` | supporting | W14 | W14 | | | | | |
| `List.Perm` (deeper) | supporting | W15 | W15 | | W15 | | | |
| `Equiv.Perm` basics | supporting | W15 | W15 | | W15 | | | |
| `Equiv.swap` | supporting | W15 | W15 | | W15 | | | |
| `Equiv.Perm.sign` | optional | W15 | W15 | | | | | Light touch only |
| `Matrix m n α` | supporting | W16 | W16 | | W16 | | | |
| `Matrix.diagonal`, `Matrix.transpose` | supporting | W16 | W16 | | W16 | | | |
| `Matrix.mul` (using Finset.sum) | supporting | W16 | W16 | | W16 | | | |
| Binomial theorem | core | W17 | | | W17 | W17 | | Capstone |
| Vandermonde identity | optional | W17 | | | W17 | | | Capstone |

### MOVE axis

| Item | Importance | I | S | R | G | T | W |
|------|-----------|---|---|---|---|---|---|
| Construct a `Fin` element (val + bound proof) | core | W1 | W1,W2 | W7 | W13 | | W1 |
| Case split on `Fin n` (`fin_cases`) | core | W1 | W1,W2 | W8 | W16 | | |
| Induction on `ℕ` (for recurrences) | core | W10 | W10 | W12,W17 | W17 | | |
| Induction on `Finset` (`Finset.induction`) | core | W11 | W11 | W13 | W17 | | |
| Membership chasing (`mem_insert`, `mem_union`, `mem_filter`, `mem_image`) | core | W5 | W5,W6,W7 | W8,W11 | W17 | | W5 |
| Subset chasing (prove `s ⊆ t` pointwise) | core | W6 | W6 | W8 | W9 | | |
| Extensionality for Finset (`ext_iff`) | core | W5 | W5,W6 | W7 | W8 | | |
| Split big operator at an element | core | W11 | W11 | W13 | W17 | | |
| Reindex a big operator (`sum_bij`) | supporting | W13 | W13 | W17 | W17 | | |
| Swap summation order (`sum_comm`) | supporting | W13 | W13 | | W17 | | |
| Apply homomorphism to big operator (`map_sum`) | supporting | W13 | W13 | | W17 | | |
| Peel off first/last from Fin-indexed sum | core | W13 | W13 | W17 | W17 | | |
| Cardinality comparison argument | core | W9 | W9 | W10 | W17 | W10 | |
| Double counting / bijection-based counting | core | W9 | W10 | W12 | W17 | W17 | |
| Induction on list (`List.rec`) | supporting | W3 | W3 | W4 | W15 | | |
| Use `DecidableEq` to enable operations | supporting | W5 | W5 | W7 | | | W5 |
| Empty-type elimination (`Fin 0` is absurd) | core | W1 | W1 | W8 | | | |
| Filter-then-sum decomposition | core | W11 | W11,W13 | W13 | W17 | | |
| Prove disjointness then apply `sum_union` | core | W11 | W11 | W13 | W17 | | W11 |

### LEAN axis

| Item | Importance | I | S | R | G | T | W |
|------|-----------|---|---|---|---|---|---|
| `omega` (for Fin/Nat bounds) | core | W1 | W1,W2 | everywhere | everywhere | | |
| `simp` / `simp only` (controlled use) | core | NNG4 baseline | W5 | everywhere | | | |
| `ext` (Finset extensionality) | core | W5 | W5,W6 | W7 | W8 | | |
| `decide` (for small finite computations) | supporting | W1 | W1 | W8 | | | W1 |
| `norm_num` (for numeric goals) | supporting | W1 | W1 | W9,W10 | | | |
| `constructor` / `And.intro` | core | NNG4 baseline | W6 | W9 | | | |
| `rcases` / `obtain` (destructuring) | core | NNG4 baseline | W5 | W7 | W13 | | |
| `use` (provide existential witness) | core | NNG4 baseline | W5 | W9 | | | |
| `rfl` | core | NNG4 baseline | everywhere | | | | |
| `congr` | supporting | W6 | W6 | W11 | | | |
| `calc` (for chain equalities) | supporting | W9 | W9 | W10 | W17 | | |
| `ring` (for algebraic simplification) | supporting | W10 | W10 | W11 | W17 | | |
| `induction ... with` (structured) | core | W3 | W3,W10,W11 | W12,W17 | W17 | | |
| `gcongr` (for inequality chains) | supporting | W9 | W9 | W10 | | | |
| Anonymous constructor `⟨_, _⟩` | core | W1 | W1,W5 | everywhere | | | |

### NOTATION axis

| Item | Importance | I | S | R | G | T | W |
|------|-----------|---|---|---|---|---|---|
| `(⟨val, proof⟩ : Fin n)` construction | core | W1 | W1 | W2 | | | W1 |
| `↑` coercion (Fin → ℕ) | core | W1 | W1,W2 | W11 | W13 | | W1 |
| `∈` for Finset membership | core | W5 | W5 | everywhere | | | |
| `∪`, `∩`, `\` for Finset operations | core | W6 | W6 | W8 | W11 | | W6 |
| `⊆` for Finset subset | core | W6 | W6 | W8 | | | |
| `∑ x ∈ s, f x` big sum notation | core | W11 | W11 | W13 | W17 | | W11 |
| `∏ x ∈ s, f x` big product notation | core | W11 | W11 | W13 | W17 | | |
| `∑ x : Fin n, f x` (Fintype-based sum) | core | W13 | W13 | W17 | W17 | | W13 |
| `Finset.range n` vs `Finset.univ (Fin n)` | core | W8 | W8,W11 | W13 | | | W8 |
| `×ˢ` for Finset.product | supporting | W7 | W7 | W13 | | | |
| `α →₀ M` for Finsupp | supporting | W14 | W14 | | | | |
| `!![a, b; c, d]` matrix notation | supporting | W16 | W16 | | | | |
| `![a, b, c]` vector/tuple notation | supporting | W2 | W2 | W16 | | | |
| `#s` for Finset.card (in Finset locale) | supporting | W9 | W9 | W10 | | | |
| Set-builder `{x ∈ s | p x}` for Finset.filter | core | W6 | W6 | W11 | | | W6 |
| `s.card` dot notation | core | W9 | W9 | everywhere | | | |

### MISCONCEPTION axis

| Item | Importance | Where addressed |
|------|-----------|----------------|
| `Fin n` elements are not natural numbers — they carry a bound proof | core | W1 |
| `Fin.val` is the coercion, not the element itself — equality on Fin uses `Fin.ext` | core | W1 |
| `Fin 0` is empty, not a type with one element | core | W1 |
| Fin arithmetic wraps modularly — `(n-1 : Fin n) + 1 ≠ n` | core | W2 |
| `List [1, 1, 2]` and `{1, 2} : Finset` have different cardinalities — duplicates are dropped | core | W3,W4 |
| `Multiset` tracks multiplicity; `Finset` does not | core | W4 |
| `Finset.image f s` may have fewer elements than `s` if `f` is not injective | core | W7 |
| `card (s ∪ t) ≠ card s + card t` in general — need disjointness or inclusion-exclusion | core | W9 |
| Finset `∪`/`∩`/`⊆` have lattice aliases (`⊔`/`⊓`/`≤`) — `sup_comm`, `inf_le_left`, etc. apply and can bypass intended reasoning | core | W6 |
| `∑ x ∈ s, f x` requires `add_comm_monoid` — cannot sum over non-commutative operations | supporting | W11 |
| `Finset.range n` contains `{0, ..., n-1}`, not `{1, ..., n}` — off-by-one | core | W5 |
| `Finset.cons` vs `Finset.insert` — cons requires non-membership proof upfront | supporting | W5 |
| Matrix multiplication is not commutative — even for 2×2 matrices | supporting | W16 |
| `Nat.choose n k = 0` when `k > n`, not undefined | supporting | W10 |

### TRANSFER axis

| Item | Importance | Where addressed |
|------|-----------|----------------|
| "To prove two finite sets are equal, show they have the same elements" — extensionality | core | W5,W6 |
| "To prove a property holds for all elements of Fin n, check each case" | core | W1,W2 |
| "To count the elements of a union, subtract the overlap" — inclusion-exclusion | core | W9 |
| "If there are more pigeons than holes, some hole has two pigeons" | core | W9,W10 |
| "To evaluate a finite sum, peel off one term and recurse" — induction shape | core | W11 |
| "To show a finite sum equals another, reindex via a bijection" | core | W13 |
| "The number of k-element subsets of an n-element set is C(n,k)" | core | W12 |
| "Factorial counts arrangements; choose counts selections" | core | W10 |
| "A finitely-supported function is determined by its values on its support" | supporting | W14 |
| "The binomial theorem is a sum over all ways to choose k items from n" | core | W17 |

### EXAMPLE axis

| Object | Role | Where used | What it concretizes |
|--------|------|-----------|-------------------|
| `Fin 3` = {0, 1, 2} | concretization | W1,W2 | Fin type, element construction, ordering |
| `Fin 0` | counterexample | W1 | Empty type — no elements exist |
| `Fin 1` | edge case | W1 | Unique element, subsingleton |
| `Fin 2` ≃ `Bool` | concretization + equivalence | W2,W8 | Fintype, equivalences between finite types |
| `{1, 2, 3} : Finset ℕ` | concretization | W5,W6 | Finset construction, operations |
| `{1, 2} ∪ {2, 3} = {1, 2, 3}` | concretization | W6 | Union, intersection overlap |
| `{1, 2} ∩ {2, 3} = {2}` | concretization | W6 | Intersection |
| `Finset.range 5 = {0,1,2,3,4}` | concretization | W5 | Range, off-by-one |
| `[1, 1, 2]` as List vs Multiset vs Finset | counterexample | W3,W4 | Duplicates lost in conversion |
| `Finset.image (· % 3) {0,1,2,3,4,5}` losing elements | counterexample | W7 | Non-injective image shrinks |
| Pascal's triangle row 4: `1, 4, 6, 4, 1` | concretization | W10 | Choose values, symmetry, Pascal's recurrence |
| `4! = 24` | concretization | W10 | Factorial computation |
| `∑ i in Finset.range 4, i = 6` (triangular number) | concretization | W11 | Finite sum evaluation |
| `∏ i in Finset.range 4, (i + 1) = 24 = 4!` | concretization | W11 | Product as factorial |
| `({1,2,3}).powerset` = 8 elements | concretization | W12 | Powerset, card = 2^n |
| `({1,2,3}).powersetCard 2` = `{{1,2},{1,3},{2,3}}` | concretization | W12 | k-element subsets = C(3,2) |
| `swap (0 : Fin 3) 1` as a permutation | concretization | W15 | Concrete transposition |
| `!![1, 0; 0, 1]` (2×2 identity matrix) | concretization | W16 | Identity matrix, multiplication |
| `!![1, 2; 3, 4] * !![0, 1; 1, 0] ≠ !![0, 1; 1, 0] * !![1, 2; 3, 4]` | counterexample | W16 | Matrix multiplication non-commutative |
| `∑ k in Finset.range (n+1), Nat.choose n k = 2^n` | concretization + integration | W17 | Binomial theorem at x=1 |

---

## 2. Core items that must not be missed

These are the items where weak coverage would make the course fundamentally incomplete.

### Must-teach definitions
1. **`Fin n`** — the entire course rests on this
2. **`Finset α`** — the central data structure
3. **`Fintype`** — the typeclass that makes `univ` and `card` work
4. **`Finset.card`** — counting is the payoff
5. **`Nat.choose`** — Pascal's triangle, subset counting
6. **`Nat.factorial`** — arrangement counting
7. **`Finset.sum` / `Finset.prod`** — big operators are where finite math meets algebra
8. **`Finset.powerset`** — subsets of a finite set

### Must-teach proof moves
1. **Finset.induction** — the primary induction principle for Finset
2. **Membership chasing** — the dominant proof pattern for Finset lemmas
3. **Extensionality** — the way to prove Finset equality
4. **Big operator splitting** — `sum_insert`, `sum_union`, `sum_filter`
5. **Case analysis on Fin** — `fin_cases` and `Fin.cases`
6. **Cardinality comparison** — pigeonhole and monotonicity
7. **Peeling off first/last from Fin-indexed sum** — `Fin.sum_univ_succ`

### Must-teach notation
1. `∑` and `∏` notation
2. `∈` for Finset
3. `∪`, `∩`, `\` for Finset
4. `⊆` for Finset
5. Fin coercion `↑`

### Must-address misconceptions
1. Fin vs ℕ confusion
2. Duplicates dropped in Finset conversion
3. Non-injective image shrinks cardinality
4. Union cardinality is not additive without disjointness
5. Lattice aliases bypassing intended Finset reasoning
6. `Finset.range n` is `{0, ..., n-1}` not `{1, ..., n}`

---

## 3. Example plan

### Definitions needing concrete examples

| Definition | Concrete example | Counterexample | World |
|-----------|-----------------|----------------|-------|
| `Fin n` | `Fin 3` — enumerate 0, 1, 2 | `Fin 0` — empty type | W1 |
| `Finset` membership | `3 ∈ {1, 2, 3}` | `4 ∉ {1, 2, 3}` | W5 |
| `Finset.union` | `{1,2} ∪ {2,3} = {1,2,3}` | — | W6 |
| `Finset.inter` | `{1,2} ∩ {2,3} = {2}` | `{1,2} ∩ {3,4} = ∅` | W6 |
| `Finset.filter` | `Finset.filter Even {1,2,3,4} = {2,4}` | — | W6 |
| `Finset.image` | `Finset.image (· + 1) {0,1,2} = {1,2,3}` | `Finset.image (· % 2) {0,1,2} = {0,1}` (lost element) | W7 |
| `Finset.card` | `card {1,2,3} = 3` | `card ({1,2} ∪ {2,3}) = 3 ≠ 2 + 2` | W9 |
| `Nat.factorial` | `4! = 24` | — | W10 |
| `Nat.choose` | `Nat.choose 4 2 = 6` (Pascal row) | `Nat.choose 3 5 = 0` (k > n) | W10 |
| `Finset.powerset` | `({1,2}).powerset = {∅, {1}, {2}, {1,2}}` | — | W12 |
| `Finset.sum` | `∑ i in Finset.range 4, i = 6` | — | W11 |
| `Finset.prod` | `∏ i in Finset.range 4, (i+1) = 24` | — | W11 |
| `Finsupp` | The function `f : ℕ →₀ ℤ` with `f 3 = 5, f 7 = -2` and 0 elsewhere | — | W14 |
| `Matrix` | 2×2 identity `!![1,0;0,1]` | Non-commutative product of two 2×2 matrices | W16 |
| `Equiv.Perm` | `swap 0 1 : Equiv.Perm (Fin 3)` | — | W15 |

### Examples that should be revisited across worlds

- **`Fin 3`**: first as a type (W1), then as index type for tuples (W2), then for `Finset.univ` (W8), then as index for a sum (W13), then for a permutation (W15), then as matrix index (W16)
- **`Finset.range n`**: first as construction (W5), then for cardinality (W9), then as summation domain (W11), then in counting identities (W17)
- **Pascal's triangle**: first as `Nat.choose` values (W10), then via `card_powersetCard` (W12), then in the binomial theorem (W17)

---

## 4. Proof-move clusters

These are groups of proof moves that naturally appear together and should be taught in proximity. Each cluster is a candidate for the center of gravity of a world or part of a world.

### Cluster A: Fin element construction and case analysis
- Construct `(⟨val, proof⟩ : Fin n)` with a bound proof
- Use `omega` to discharge bound obligations
- Use `fin_cases` to enumerate all elements of small `Fin n`
- Use `Fin.ext` to prove equality of Fin elements
- Eliminate `Fin 0` via `finZeroElim` / `Fin.elim0`

**Dominant move:** case split on a finite type.
**World:** W1

### Cluster B: Fin successor structure and casting
- Use `Fin.succ`, `Fin.castSucc`, `Fin.cast` to relate `Fin n` and `Fin (n+1)`
- Reason about `Fin.last n`
- Use `Fin.cons` / `Fin.snoc` to build tuples
- Decompose via `Fin.cases` (first element vs rest)
- Understand modular arithmetic on Fin

**Dominant move:** relate elements across different `Fin n`.
**World:** W2

### Cluster C: List structural reasoning
- Pattern match on `[]` vs `a :: l`
- Use `List.length` in equalities
- Apply `List.map` and `List.filter` and reason about their output
- Prove membership via `List.mem_cons` and `List.mem_append`
- Use `List.rec` / structural induction on lists

**Dominant move:** structural induction on a list.
**World:** W3

### Cluster D: Multiset and conversion pipeline
- Understand `Multiset` as order-forgetting quotient of `List`
- Use `List.toFinset`, `Multiset.toFinset`
- Reason about `Nodup` as the bridge condition
- See that conversion drops duplicates

**Dominant move:** convert between representations and track what is lost.
**World:** W4

### Cluster E: Finset membership and construction
- Prove `a ∈ insert b s` via `mem_insert`
- Prove `a ∈ {b}` via `mem_singleton`
- Prove `a ∈ Finset.range n` via `mem_range`
- Use `Finset.ext_iff` (prove `∀ x, x ∈ s ↔ x ∈ t`)
- Understand `DecidableEq` requirement

**Dominant move:** membership chasing.
**World:** W5

### Cluster F: Finset set operations
- Use `mem_union`, `mem_inter`, `mem_sdiff`, `mem_filter` to decompose membership
- Prove `s ⊆ t` by `intro x hx; ...`
- Prove disjointness via `Finset.disjoint_left`
- Combine: given `s ⊆ t` and `a ∈ s`, conclude `a ∈ t`
- Watch for lattice aliases (`sup_comm` = `union_comm`, etc.)

**Dominant move:** subset/membership reasoning with set operations.
**World:** W6

### Cluster G: Image, map, and products
- Use `mem_image` to prove membership in `Finset.image`
- Use `mem_map` for embeddings
- Understand `Finset.product` membership: `mem_product`
- See that non-injective `image` can shrink
- See that `map` preserves cardinality

**Dominant move:** transform a Finset and track membership.
**World:** W7

### Cluster H: Fintype and universal sets
- Recognize when `[Fintype α]` is available
- Use `Finset.univ` as the "everything" set
- Relate `Fintype.card α` to `Finset.card Finset.univ`
- Know common instances: `Fin`, `Bool`, `Prod`, `Sum`, `Subtype`
- Distinguish `Finset.range n` from `Finset.univ (α := Fin n)`

**Dominant move:** use the Fintype class to work with universal sets.
**World:** W8

### Cluster I: Cardinality and counting
- Use `card_empty`, `card_singleton`, `card_insert_of_not_mem`
- Apply `card_union_add_card_inter` (inclusion-exclusion)
- Use `card_le_card` (monotonicity for subsets)
- Use `card_image_of_injective`
- Apply pigeonhole: if `card s > card t` and `f : s → t`, then f is not injective

**Dominant move:** cardinality-based argument.
**World:** W9

### Cluster J: Factorial and choose manipulation
- Unfold `Nat.factorial` recursively
- Use Pascal's recurrence: `choose (n+1) (k+1) = choose n k + choose n (k+1)`
- Use `choose_eq_factorial_div_factorial`
- Use `choose_symm`
- Induction on `n` for factorial/choose identities

**Dominant move:** inductive identity proof.
**World:** W10

### Cluster K: Big operator basics
- Write `∑ x ∈ s, f x` and `∏ x ∈ s, f x`
- Use `sum_empty`, `sum_singleton`, `sum_insert`
- Use `sum_union` with disjointness
- Use `sum_filter` to restrict summation
- Use `sum_const` and `sum_range`
- Use `Finset.induction` to prove identities about sums

**Dominant move:** decompose and reassemble a finite sum.
**World:** W11

### Cluster L: Advanced big operator manipulation
- Use `sum_bij` / `prod_bij` for bijective reindexing
- Use `sum_comm` to swap summation order
- Use `sum_sigma` for iterated sums
- Use `Fin.sum_univ_succ` to peel off first/last element
- Use `map_sum` / `map_prod` with homomorphisms

**Dominant move:** structural rewriting of big operators.
**World:** W13

### Cluster M: Counting identity integration
- Combine big operators with choose/factorial
- Prove binomial theorem
- Use double counting (prove sum from two directions)
- Connect `card_powersetCard` to `Nat.choose`
- Stars and bars via `multichoose`

**Dominant move:** combine all prior machinery for an identity.
**World:** W17

---

## 5. Novelty hotspots

Places where novelty would concentrate dangerously if not sequenced carefully.

### Hotspot 1: W1 (Fin)
**Risk:** New math (Fin type) + new notation (⟨val, proof⟩, ↑ coercion) + new tactic (`omega`) simultaneously.
**Mitigation:** Split W1 into levels that isolate each piece. First level: just Fin.mk and val. Second level: introduce ↑ coercion. Third level: introduce omega for bound proofs. Fourth level: fin_cases.

### Hotspot 2: W5 (Finset basics)
**Risk:** New math (Finset type) + new notation (∈ for Finset, set-builder {x ∈ s | p x}) + new Lean move (ext) + new proof pattern (membership chasing).
**Mitigation:** Introduce Finset with trivially simple membership goals first. Then ∈ notation. Then ext separately. Then membership chasing.

### Hotspot 3: W6 (Finset operations)
**Risk:** Three new operations (∪, ∩, \) + lattice alias hazard + filter + subset reasoning all at once.
**Mitigation:** Introduce ∪ alone with simple membership proofs. Then ∩. Then \. Then filter. Then subset. Lattice aliases addressed as a dedicated warning level.

### Hotspot 4: W11 (Big operators)
**Risk:** New notation (∑, ∏) + new math (finite sums) + new proof move (Finset.induction) + new Lean tactic pattern (induction on Finset).
**Mitigation:** First level: just notation and sum_empty/sum_singleton. Second level: sum_insert with a concrete example. Third level: Finset.induction as a proof move. No new math content until the notation and proof shape are familiar.

### Hotspot 5: W10 (Factorials & Choose)
**Risk:** Two new definitions (factorial, choose) + inductive proofs + algebraic manipulation.
**Mitigation:** Introduce factorial first with concrete computation. Then choose with Pascal's recurrence as a concrete computation. Then inductive proofs separately.

### Hotspot 6: W16 (Matrices)
**Risk:** New notation (`!![a,b;c,d]`) + new math (matrix type) + matrix multiplication uses Finset.sum (integration burden).
**Mitigation:** Keep this world light. Focus on entry access and simple operations. Matrix multiplication is an integration level, not a teaching level for new moves.

---

## 6. Items to demote, delay, or hide

### Disable baseline (all levels)
`trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all`

### Disable per-level (when they bypass the intended reasoning)
- `norm_num`: disable in W1-W2 when teaching Fin element construction; enable in W10+ for factorial/choose
- `linarith`: disable in W1-W2; enable when cardinality arguments need it
- `tauto`: disable in membership-chasing levels (W5-W7) where the learner should decompose manually
- `fin_cases`: disable in W1 early levels that teach manual Fin case analysis; enable later as taught tool
- `ext`: disable until explicitly taught (W5)
- `interval_cases`: disable everywhere (bypasses Fin case analysis)
- `by_cases`: disable in early levels; enable when genuinely needed

### Theorem exploits to disable per-level
- `Fin.forall_fin_two`, `Fin.forall_fin_one`: disable in W1 fin_cases levels
- `Subsingleton.elim`, `Unique.eq_default`: disable in W1 Fin 1 levels
- **Lattice aliases** (W6): `sup_comm`, `inf_le_left`, `le_antisymm`, `sup_le`, `sup_eq_left`, `inf_comm`, `bot_sup_eq`, `sup_bot_eq`, etc. — disable when teaching the Finset-specific versions (`union_comm`, `inter_subset_left`, etc.)
- `Finset.subset_iff`: potentially disable when teaching pointwise subset proofs

### Items to delay
- `Finsupp` (W14): delay until big operators are solid. Finsupp is useful but secondary to Finset.
- `Equiv.Perm` (W15): delay until after counting. The group structure belongs in the group theory course; here we only touch permutations as counting objects.
- `Matrix` (W16): delay until after big operators. Matrix multiplication requires Finset.sum, so this world is inherently integrative.

### Items to keep out of inventory but use implicitly
- `Multiset.Nodup`: used internally in Finset construction but not directly manipulated by the learner
- `Finset.val`: the underlying Multiset — too low-level for most levels
- `Finset.fold`: subsumed by big operators in pedagogical context

---

## 7. Confidence notes

### High confidence
- **Fin, Finset, Fintype, big operators, choose, factorial** — these are the backbone of the course and the mathlib API is mature, well-documented, and stable. The proof-move clusters I've identified are grounded in how these APIs are actually used.
- **Lattice alias hazard** — this is a known, documented exploit vector. The operational lessons confirm it.
- **Novelty hotspots at W1, W5, W6, W11** — these are the natural pinch points where multiple new things converge.
- **Example plan** — the concrete objects (`Fin 3`, `{1,2,3}`, Pascal's triangle, etc.) are natural and unavoidable.

### Needs architect judgment
- **World count (17 worlds)**: This is a large course. The architect should decide whether W14 (Finsupp), W15 (Permutations), and W16 (Matrices) are worth including or should be cut to keep the course focused. The course description includes them, but they could be "bonus" worlds rather than required progression.
- **Depth of W15 (Permutations)**: How much `Equiv.Perm` to include? The sign, cycle decomposition, and support are all in mathlib but may duplicate the group theory course. I've marked these as supporting/optional but the architect should decide.
- **Depth of W16 (Matrices)**: Matrix multiplication is genuinely integrative (it uses Finset.sum over Fin indices), but the full matrix API is enormous. I've limited scope to basic entry access, diagonal, transpose, and multiplication. The architect should confirm this boundary.
- **Whether W17 (Counting Identities) should include Vandermonde**: Vandermonde is a beautiful capstone but may be too hard if the learner hasn't internalized bijective reindexing (`sum_bij`). The architect should judge difficulty.
- **Multiset depth (W4)**: Multisets are mathematically important as the bridge between lists and finsets, but the learner may find them unmotivating. The architect should decide whether to keep W4 as a standalone world or merge it into W3.
- **`omega` availability**: `omega` solves most Fin/Nat bound goals instantly. If it's always available, many Fin levels become trivial. If it's disabled, the learner needs to do manual bound manipulation (which is tedious but educational). The architect should decide the policy.
- **Finset.induction vs Finset.cons/insert induction**: There are multiple induction principles for Finset. I've centered on `Finset.induction` (insert-based) as the primary one. The architect should confirm this is the right choice.

### Low confidence / uncertain
- **Exact API names for some big-operator lemmas**: The mathlib4 big-operator module has been reorganized multiple times. Some lemma names (e.g., `sum_ite` vs `sum_filter_add_sum_filter_not`) may have changed. The architect should verify exact names against the project's mathlib version before authoring levels.
- **`Finset.product` notation `×ˢ`**: I've seen this notation in mathlib but I'm not certain it's in the default scope for the GameServer. The architect should verify.
- **`!![a,b;c,d]` matrix notation**: This notation exists in mathlib (`Matrix.of`) but I'm not certain of the exact import path or whether it works smoothly in the GameServer environment. The architect should test before committing to it.

---

## Appendix: Proposed world structure

| # | World | Center of gravity | Key proof-move cluster |
|---|-------|-------------------|----------------------|
| W1 | Fin — The Finite Type | Constructing and reasoning about Fin n elements | Cluster A |
| W2 | Fin Successors & Tuples | Relating Fin n and Fin (n+1); tuples | Cluster B |
| W3 | Lists | Ordered finite sequences; structural induction | Cluster C |
| W4 | Multisets & Conversion | Unordered bags; List → Multiset → Finset pipeline | Cluster D |
| W5 | Finset Construction | Building finsets; membership; extensionality | Cluster E |
| W6 | Finset Operations | Union, inter, sdiff, filter, subset | Cluster F |
| W7 | Finset Transformations | Image, map, product, sigma | Cluster G |
| W8 | Fintype & Universal Sets | Fintype class; univ; card | Cluster H |
| W9 | Cardinality | Finset.card; counting; pigeonhole | Cluster I |
| W10 | Factorials & Binomial Coefficients | Nat.factorial, Nat.choose, identities | Cluster J |
| W11 | Big Operators I — Basics | ∑ and ∏ notation; basic manipulation | Cluster K |
| W12 | Powerset & Subset Counting | Powerset, powersetCard, card connections | (uses Clusters I, J) |
| W13 | Big Operators II — Advanced | Reindexing, iterated sums, Fin-indexed sums | Cluster L |
| W14 | Finitely Supported Functions | Finsupp basics | (standalone) |
| W15 | Permutations | List.Perm, Equiv.Perm basics, counting | (standalone) |
| W16 | Matrices over Fin | Matrix type, operations, multiplication | (integration) |
| W17 | Counting Identities | Binomial theorem, double counting | Cluster M |

### Dependency graph

```
W1 → W2 → W3 → W4 → W5 → W6 → W7 → W8
                                       ↓
                                      W9 → W10 → W12
                                       ↓          ↓
                                      W11 → W13 → W17
                                       ↓
                                      W14
                                      W15
                                      W16
```

W14, W15, W16 are semi-independent: they require W11 (big operators) and W8 (Fintype) but not each other.
W17 requires W10, W12, and W13.
