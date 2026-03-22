# Coverage Review: finite_math

**Reviewed**: 2026-03-20
**Artifact**: `finite_math/coverage-map.md`
**Reference**: `long_term.md` entry #1

---

## 1. Scope Gaps

### Checked against `long_term.md` description

The course description says:

> `Fin`, `Fintype`, `Finset`, finite sets as subtypes, lists versus multisets, permutations of lists, finitely supported functions, finite products of finsets, matrices over finite index types, and the big-operator layer that turns finite objects into usable mathematics. It should also include binomial coefficients, factorials, finite sums/products, and the counting identities that underlie later combinatorics and linear algebra.

| Topic from `long_term.md` | Present in coverage map? | Notes |
|---|---|---|
| `Fin` | YES | Thoroughly covered (MATH axis rows 1-5, Cluster F, G) |
| `Fintype` | YES | Thoroughly covered (MATH axis rows 8-11) |
| `Finset` | YES | Thoroughly covered (MATH axis rows 6-16) |
| Finite sets as subtypes | YES | Via `Fintype` instances for subtypes (row 10) and `Fin n` as `{ i // i < n }` |
| Lists versus multisets | YES | Rows 13-16, Cluster H |
| Permutations of lists | YES | `List.Perm` (row 15) |
| Finitely supported functions | YES | `Finsupp` (rows 17-18) |
| Finite products of finsets | YES | `Finset.product` (row 13) |
| Matrices over finite index types | YES | `Matrix` (rows 23-24) |
| Big-operator layer | YES | `Finset.sum`/`Finset.prod` (rows 19-26) |
| Binomial coefficients | YES | `Nat.choose` (rows 28-32) |
| Factorials | YES | `Nat.factorial`, `ascFactorial`, `descFactorial` (rows 27-28) |
| Finite sums/products | YES | Covered by big operators |
| Counting identities | YES | Pascal's, binomial theorem, sum-of-row, inclusion-exclusion (rows 33-36) |

**No scope gaps found.** All topics from `long_term.md` are represented in the coverage map.

### Minor observation

`Finset.erase` is not listed in the MATH axis, though `Finset.insert` is. `erase` is the reverse operation, and `card_erase_of_mem` is a useful cardinality lemma. This is not P0 — `erase` can be introduced through `sdiff` with a singleton — but it's worth noting for world authoring.

---

## 2. Mathlib Discrepancies

I verified current mathlib4 API names against the coverage map. Here are the findings:

### Confirmed correct names

| Coverage map name | Status |
|---|---|
| `Fin.val`, `Fin.castSucc`, `Fin.succ`, `Fin.last` | Correct |
| `Fin.cons`, `Fin.snoc` | Correct |
| `Finset.mem`, `Finset.subset`, `Finset.empty`, `Finset.singleton`, `Finset.insert` | Correct |
| `Finset.union`, `Finset.inter`, `Finset.sdiff` | Correct |
| `Finset.filter`, `Finset.image`, `Finset.map` | Correct |
| `Finset.card` | Correct |
| `Finset.range`, `Finset.powerset`, `Finset.powersetCard` | Correct |
| `Finset.product`, `Finset.sigma` | Correct |
| `Finset.diag`, `Finset.offDiag` | Correct |
| `Fintype.card`, `Finset.univ` | Correct |
| `Fintype.card_fin`, `Fintype.card_prod`, `Fintype.card_sum` | Correct |
| `Fintype.card_fun`, `Fintype.card_pi` | Correct |
| `Multiset.card`, `Multiset.count` | Correct |
| `List.Perm`, `List.Nodup` | Correct |
| `Finsupp`, `Finsupp.support`, `Finsupp.single`, `Finsupp.mapDomain` | Correct |
| `Finset.sum`, `Finset.prod` | Correct |
| `Finset.sum_empty`, `Finset.sum_singleton`, `Finset.sum_insert` | Correct |
| `Finset.sum_congr`, `Finset.prod_congr` | Correct |
| `Finset.sum_const`, `Finset.prod_const` | Correct |
| `Finset.sum_add_distrib`, `Finset.prod_mul_distrib` | Correct |
| `Finset.card_insert_of_notMem` | Correct (camelCase) |
| `Finset.card_union_add_card_inter` | Correct |
| `Finset.card_powerset`, `Finset.card_powersetCard` | Correct |
| `Finset.card_product` | Correct |
| `Finset.card_image_of_injOn`, `Finset.card_image_le` | Correct |
| `Nat.choose`, `Nat.choose_succ_succ`, `Nat.choose_symm` | Correct |
| `Nat.choose_eq_factorial_div_factorial` | Correct |
| `Nat.multichoose` | Correct |
| `Nat.factorial`, `Nat.ascFactorial`, `Nat.descFactorial` | Correct |
| `Nat.sum_range_choose` | Correct |
| `add_pow` | Correct (for commutative semirings) |
| `Finset.cons_induction`, `Finset.induction_on` | Correct |
| `Fintype.card_congr` | Correct |
| `Matrix` as `m → n → α` | Correct |

### Discrepancies

| Coverage map name | Actual current name | Severity |
|---|---|---|
| `Finset.sum_fiberwise` / `Finset.prod_fiberwise` | `Finset.sum_fiberwise_of_maps_to` and `Finset.sum_fiberwise_eq_sum_filter` (similarly for `prod`) | **Low** — the coverage map uses shortened names. The actual API has two variants depending on whether a `maps_to` hypothesis is available. Update the map to use the full names. |
| `Finset.sum_image` / `Finset.prod_image` | These exist but may be named `Finset.sum_nbij` or similar in some contexts | **Low** — verify at authoring time. `sum_image` does exist as a name. |
| `Fintype.piFinset` | May be `Fintype.piFinset` or accessed through `Finset.pi` | **Low** — verify at authoring time. |

### Missing mathlib content worth considering

| Item | Why it matters |
|---|---|
| `Finset.card_sdiff` / `Finset.card_sdiff_of_subset` | Listed in Cluster B but not in the MATH axis rows. These are important cardinality lemmas. |
| `Finset.Nonempty` | Used in Cluster A ("choose from nonempty finset") but not listed in the MATH axis. |
| `Finset.card_mono` | Listed in Core Items (section 2) but not in the MATH axis. |
| `Finset.card_lt_card` | Listed in MOVE axis (pigeonhole) but not in MATH axis. |
| `Finset.card_le_of_subset` | Alias for `card_mono`; not explicitly listed. |
| `Commute.add_pow` | The non-commutative version of the binomial theorem. Not needed for this course but worth knowing about. |

**None of these are P0.** The coverage map uses the items in proof-move clusters and core items lists even if they don't appear as separate MATH axis rows. The MATH axis is not intended to be exhaustive of every lemma — it covers definitions and major theorem families.

---

## 3. Proof-Move Gaps

### Clusters reviewed

| Cluster | Realistic? | Notes |
|---|---|---|
| A: Membership and containment | YES | Standard proof pattern. Theorem families correctly identified. |
| B: Cardinality arithmetic | YES | Correctly identifies the key `card_*` lemmas. |
| C: Induction on finsets | YES | `cons_induction` / `induction_on` correctly identified. The `a ∉ s` hypothesis shape is a real pedagogical challenge. |
| D: Big-operator manipulation | YES | Correctly identifies the key moves. |
| E: Combinatorial identities via big operators | YES | Good identification that this requires Clusters C+D combined. |
| F: Fin navigation and case analysis | YES | Correctly identifies `Fin.val_*`, `Fin.mk_*`, `Fin.ext_iff`. |
| G: Tuple construction and manipulation | YES | `Fin.cons`/`Fin.snoc`/`Fin.tail` are the right primitives. |
| H: List → Multiset → Finset pipeline | YES | Correctly frames the abstraction ladder. |
| I: Equivalences and cardinality transfer | YES | `Fintype.card_congr` is the right workhorse. |

### Missing proof-move patterns

| Pattern | Where it fits | Severity |
|---|---|---|
| **Decidability reasoning** | Listed in MOVE axis row 17 but not a named cluster. In practice, `Decidable` goals arise when constructing `Finset` terms over new types or using `Finset.filter`. Could be folded into Cluster A or mentioned in Hotspot 1. | **Low** — correctly identified in the MOVE axis, just not clustered. |
| **`omega` for Fin/ℕ goals** | Listed in LEAN axis but not clustered. `omega` is the primary closer for `Fin` arithmetic and many `card` goals. Interacts with Clusters B and F. | **Low** — covered in LEAN axis. |

**No significant proof-move gaps found.** The 9 clusters cover the major proof shapes for this course.

---

## 4. Example Gaps

### Definitions checked for examples

| Definition | Has concrete examples? | Has counterexamples? | Verdict |
|---|---|---|---|
| `Fin n` | YES (Fin 0-4) | N/A | Good |
| `Finset` | YES ({1,2,3}, ∅, range, univ) | N/A | Good |
| `Finset.card` | YES | YES (non-injective image) | Good |
| `Finset.powerset` | YES | N/A | Good |
| `Finset.powersetCard` | YES | YES (k > n gives ∅) | Good |
| `Multiset` | YES | YES (vs Finset) | Good |
| `List` | YES | YES (vs Multiset) | Good |
| `List.Perm` | YES | YES | Good |
| `List.Nodup` | YES | YES | Good |
| `Fintype` | YES | YES (ℕ is not Fintype) | Good |
| `Nat.choose` | YES (boundary cases) | YES (k > n) | Good |
| `Nat.factorial` | YES (0! = 1) | N/A | Good |
| `Finset.sum` | YES | YES (empty = 0) | Good |
| `Finset.prod` | YES | YES (empty = 1) | Good |
| `Matrix` | YES (2×2) | N/A | Good |
| `Finsupp` | YES (single) | N/A | Good |
| `Finset.product` | YES (enumerate pairs) | N/A | Good |
| `add_pow` | YES (small expansion) | N/A | Good |
| `Finset.Nat.antidiagonal` | YES | N/A | Good |
| `Finset.sigma` | NO | NO | See below |
| `Finset.disjUnion` | NO | NO | See below |

### Gaps

| Item | Issue | Severity |
|---|---|---|
| `Finset.sigma` | No planned example. Listed as "supporting" and delayed, so this is acceptable. | **Low** |
| `Finset.disjUnion` | No planned example. Listed as "hidden", so this is acceptable. | **Low** |
| `Finsupp.mapDomain` | Listed in MATH axis but no example in Example Plan. | **Low** — Finsupp is "supporting" and recommended for minimal treatment. |

**No significant example gaps found.** The example plan is thorough, with good variety of concretizations, counterexamples, and boundary cases for all core definitions.

---

## 5. Exploit Gaps

### Identified exploit vectors in the coverage map

| Exploit | Status | Notes |
|---|---|---|
| `simp` (baseline disabled) | YES | Correctly identified |
| `decide` | YES | Correctly identified for gating |
| `norm_num` | YES | Correctly identified for gating |
| `fin_cases` | YES | Correctly identified for gating |
| `interval_cases` | YES | Correctly identified |
| `ext` | YES | Correctly identified for selective gating |
| Lattice aliases (`sup_comm`, `inf_comm`, `inf_le_left`, etc.) | YES | Correctly identified as always-disable when Finset ∪/∩ are the topic |
| `trivial`, `native_decide`, `aesop`, `simp_all` | YES (via baseline) | From CLAUDE.md baseline |

### Missing exploit vectors

| Exploit | Why it matters | Severity |
|---|---|---|
| `tauto` | Can close propositional membership goals (`x ∈ s ∨ x ∈ t` style). Mentioned in CLAUDE.md operational lessons but not in the coverage map's gate table. | **Low** — most Finset goals are not pure propositional, but `tauto` can close some `mem_union` / `mem_inter` goals. Add to gate table. |
| `omega` | Listed as a LEAN axis tool but NOT in the gate table. `omega` can one-shot many `Fin` arithmetic goals and `card` equality goals. Should be gated when manual arithmetic is the lesson. | **Medium** — `omega` is the most powerful uncontrolled automation for ℕ/Fin goals in this course. Add to gate table with guidance on when to disable. |
| `Finset.ext_iff` / `Finset.ext_iff'` | `simp [Finset.ext_iff]` can reduce set equality to membership, which `decide` then closes. The combination bypasses the intended manual `ext` + membership reasoning. | **Low** — mitigated by baseline `simp` disable, but worth noting. |
| `by_contra` + `Finset.not_mem_empty` | Can bypass constructive membership proofs. | **Low** — situational. |
| Specific library lemmas: `Finset.subset_univ`, `Finset.empty_subset`, `Finset.union_comm`, `Finset.inter_comm` | These are direct-apply lemmas that can one-shot levels intended to teach the underlying reasoning. At authoring time, the author should check whether `exact Finset.union_comm s t` bypasses the level. | **Low** — this is a per-level concern, not a coverage-map concern. The map correctly identifies the lattice alias problem, which is the systematic version of this. |

### Key finding on `omega`

The coverage map lists `omega` in the LEAN axis as a core tool (row 2) but does NOT include it in the gate table (Section 6). Since `omega` closes most `Fin.val` arithmetic goals and many `Finset.card` equality goals over concrete numbers, it should be in the gate table with a note like:

> Gate `omega` when manual Fin/ℕ arithmetic reasoning is the lesson. `omega` is the dominant closer for goals of the form `i.val < n`, `card s = k`, and `a + b = c` over ℕ.

**Severity: Medium.** Not P0 because the author can catch this at level-authoring time, but it should be documented in the map to prevent oversight.

---

## 6. Overall Verdict

**PASS**

The coverage map is thorough, well-organized, and accurately reflects both the `long_term.md` scope and the current mathlib4 API. All core topics are covered, proof-move clusters are realistic, the example plan is comprehensive, and exploit vectors are well-identified.

### Items to address before world authoring (non-blocking)

1. **Update `Finset.sum_fiberwise` / `Finset.prod_fiberwise`** to use full current API names (`sum_fiberwise_of_maps_to` or `sum_fiberwise_eq_sum_filter`).
2. **Add `omega` to the gate table** (Section 6) with guidance on when to disable.
3. **Add `tauto` to the gate table** as a minor exploit vector for propositional membership goals.
4. **Consider adding `Finset.erase`** to the MATH axis — it's the reverse of `insert` and its cardinality lemma `card_erase_of_mem` is useful.
