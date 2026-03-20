# Coverage Map Review — finite_math

**Date:** 2026-03-20
**Reviewer:** coverage-review (automated)

---

## 1. Scope gaps

### P0 — "Finite sets as subtypes" is missing entirely

The course description in `long_term.md` explicitly lists **"finite sets as subtypes"** as a core topic. The coverage map's own scope summary (line 5) repeats this phrase. Yet the coverage matrix has **zero entries** for:

- `Set.Finite` — the predicate that a `Set` is finite
- `Set.toFinset` / `Finset.toSet` — the bridge between `Set α` and `Finset α`
- `Set.Finite.toFinset` — converting a finite-set proof into a `Finset`
- The subtype `{x : α // x ∈ s}` for a finite set `s`

This is the bridge between predicate-based sets (`Set α`) and data-based finite sets (`Finset α`). It is explicitly in-scope per the course description and completely absent from the map.

**Resolution required:** Either add coverage (likely a world between W8 and W9 that covers `Finset ↔ Set.Finite` conversion), or explicitly document that this topic is deferred to course 2 (Sets/Functions/Relations) with a justification for the scope change.

### P1 — `Finset.erase` missing

`Finset.erase` is the dual of `Finset.insert`. It appears pervasively in Finset cardinality proofs (e.g., `card_erase_of_mem`, `insert_erase`, `erase_insert`). The coverage matrix covers `insert` but has no entry for `erase`. This is a meaningful gap for W5/W6/W9 where membership manipulation and cardinality arguments are taught.

### P1 — `Finset.biUnion` missing

`Finset.biUnion s f` (indexed union) generalizes binary `∪` to unions indexed over a finset. It's a standard Finset operation used in counting arguments and is the natural companion to `Finset.sigma`. Not mentioned anywhere in the coverage matrix.

### P1 — `Finset.antidiagonal` missing (needed for Vandermonde)

The Vandermonde identity (`Nat.add_choose_eq`) is listed as an optional capstone in W17. Its mathlib statement is:
```
(m + n).choose k = ∑ ij ∈ Finset.antidiagonal k, m.choose ij.1 * n.choose ij.2
```
The binomial theorem's alternative form (`Commute.add_pow'`) also uses `antidiagonal`. If either is taught, students need exposure to `Finset.antidiagonal` beforehand. The coverage map doesn't mention antidiagonal at all.

### P2 — Additional counting identities exist in mathlib

The following identities exist in `Mathlib.Data.Nat.Choose.Sum` and could enrich W17 but are not mentioned:

- `Nat.sum_Icc_choose` — the hockey-stick identity: `∑ m ∈ Icc k n, m.choose k = (n + 1).choose (k + 1)`
- `Nat.sum_range_mul_choose` — `∑ i ∈ range (n+1), i * choose n i = n * 2^(n-1)`
- `Int.alternating_sum_range_choose` — alternating sum of binomial coefficients equals 0 for n ≥ 1

These are not required, but the architect should know they exist when designing W17 content.

---

## 2. Mathlib discrepancies

### API name to verify: `card_insert_of_not_mem`

The coverage map uses `card_insert_of_not_mem` (Cluster I, line 369). Current mathlib4 documentation shows `Finset.card_insert_of_notMem` (camelCase `notMem`). This may be a naming convention change. **Verify against the project's pinned mathlib version before authoring.**

### Missing API names for capstone theorems

The coverage map lists "Binomial theorem" and "Vandermonde identity" in W17 without specifying the mathlib API names:
- **Binomial theorem:** `Commute.add_pow` (non-commutative) or `add_pow` (commutative semiring)
- **Vandermonde identity:** `Nat.add_choose_eq`

These should be recorded in the map so the author knows exactly what to target.

### Pascal's recurrence name

The coverage map describes Pascal's recurrence correctly but should note the mathlib4 name is `Nat.choose_succ_succ` (for `choose (n+1) (k+1) = choose n k + choose n (k+1)`).

### `Finset.card_powerset` and `Finset.card_powersetCard`

Confirmed: these exact names exist in current mathlib4 (`Mathlib.Data.Finset.Powerset`). No discrepancy.

### `sum_ite` name

The coverage map references `sum_ite` (line 68). The actual mathlib4 name should be verified — it may be `Finset.sum_ite` or it may have been reorganized. The related `Finset.sum_boole` (indicator-to-card conversion) is also worth checking.

---

## 3. Proof-move gaps

### Erase/insert duality

Many Finset cardinality proofs use the pattern: erase an element, prove a property of the smaller set, then reinsert. The `insert_erase` / `erase_insert` pair is central to this. Clusters E, F, and I should include this move.

### Antidiagonal-based summation

If Vandermonde is included in W17, the proof-move of "sum over antidiagonal pairs" is required and is not in any cluster. This is a genuinely different pattern from `sum_range` or `sum_univ`.

### `Finset.sum_boole` pattern

The proof move "convert a membership-counting argument into a card via `sum_boole`" (`∑ x ∈ s, if p x then 1 else 0 = (s.filter p).card`) is a common pattern. Not mentioned in any cluster. Potentially fits Cluster K or L.

---

## 4. Example gaps

### `Finset.erase`

No concrete example for `erase` since it's not in the coverage matrix. Natural example: `({1, 2, 3} : Finset ℕ).erase 2 = {1, 3}`.

### `Set.Finite` / `Set.toFinset`

No examples since the topic is entirely missing. Natural example: `{x : ℕ | x < 5}.toFinset = Finset.range 5`.

### `Finset.biUnion`

No concrete example. Natural example: `Finset.biUnion {1, 2, 3} (fun n => Finset.range n)`.

### `Finset.antidiagonal`

No concrete example. Natural example: `Finset.antidiagonal 3 = {(0,3), (1,2), (2,1), (3,0)}`.

---

## 5. Exploit gaps

### `Finset.subset_iff`

The coverage map says "potentially disable" (line 469) but doesn't commit. This lemma one-shots many subset-chasing goals that should require pointwise reasoning. **Commit to disabling it in W6 levels that teach subset proofs.**

### `Finset.mem_union` / `Finset.mem_inter` + `simp`

When `simp` lemmas for membership (`mem_union`, `mem_inter`, `mem_filter`, `mem_image`) are all tagged `@[simp]`, `simp` can close many membership goals automatically. The map notes the baseline `simp` disable, but if `simp only [...]` is available, students could still chain these. Worth noting for level authors.

### `Nat.choose_eq_factorial_div_factorial` as one-shot

In W10, if `norm_num` is enabled alongside `Nat.choose_eq_factorial_div_factorial`, many choose-value goals can be closed computationally. The map notes enabling `norm_num` in W10+ but should flag this specific interaction.

### `Finset.card_filter_le_card`

This monotonicity lemma can shortcut some pigeonhole-adjacent arguments. Not mentioned in the exploit list.

---

## 6. Overall verdict

**FAIL**

### Blocking issues (must fix):

1. **P0 — "Finite sets as subtypes"** is listed in the course scope (both `long_term.md` and the coverage map's own scope summary) but has zero coverage in the matrix. This is a core scope gap. Either add it or explicitly and justifiably remove it from scope.

2. **P1 — `Finset.erase`** is a fundamental Finset operation absent from the coverage matrix. It's the dual of `insert` and is required for many cardinality proofs. Add it to the MATH axis and Clusters E/F/I.

### Should fix (before authoring begins):

3. Add mathlib API names for the binomial theorem (`add_pow`) and Vandermonde (`Nat.add_choose_eq`) to the W17 entries.
4. Add `Finset.biUnion` to the MATH axis (W7 or a new entry in W6).
5. If Vandermonde stays in W17 (even as optional), add `Finset.antidiagonal` to the MATH axis.
6. Commit on `Finset.subset_iff` disable policy for W6.
7. Verify `card_insert_of_not_mem` name against pinned mathlib.
