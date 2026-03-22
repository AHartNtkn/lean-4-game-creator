import Game.Metadata

World "PsetCombinatorics"
Level 14

Title "Boss: Vandermonde Through Powerset"

Introduction "
# Boss: The Vandermonde Convolution via Subsets

The Vandermonde identity says:

$$\\binom{2n}{n} = \\sum_{(i,j) \\in \\text{antidiagonal}(n)}
\\binom{n}{i} \\cdot \\binom{n}{j}$$

You proved this algebraically in PascalsTriangle (Level 11)
using `Nat.add_choose_eq`. Now prove it with a **powerset layer**:

$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)}
|\\text{powersetCard } i\\ s| \\cdot |\\text{powersetCard } j\\ s|
= \\binom{2n}{n}$$

**What you need** (all from prior worlds):
- `Finset.card_powersetCard` — strip the powerset layer (Powerset)
- `Finset.sum_congr rfl` — rewrite summands pointwise (BigOpAlgebra)
- `2 * n = n + n` via `ring` — reshape for Vandermonde
- `Nat.add_choose_eq n n n` — the Vandermonde identity (PascalsTriangle)
- `symm` — flip and close (BinomialTheorem pattern)

**Proof plan**:
1. Convert each `(powersetCard _ s).card` to `choose n _`
2. Apply `sum_congr rfl` to rewrite the whole sum
3. Reshape `2 * n` as `n + n`
4. Flip and apply Vandermonde
"

/-- The Vandermonde convolution through powerset counting. -/
Statement (n : ℕ) (s : Finset ℕ) (hs : s.card = n) :
    ∑ p ∈ Finset.antidiagonal n,
      (Finset.powersetCard p.1 s).card * (Finset.powersetCard p.2 s).card =
    Nat.choose (2 * n) n := by
  Hint "Strip the powerset layer from each summand. Use
  `Finset.sum_congr rfl` with a pointwise proof that converts
  `(powersetCard _ s).card` to `choose n _`."
  Hint (hidden := true) "Declare:
  `have simpl : ∀ p ∈ Finset.antidiagonal n, (Finset.powersetCard p.1 s).card * (Finset.powersetCard p.2 s).card = Nat.choose n p.1 * Nat.choose n p.2 := by`

  Then: `intro p _` followed by
  `rw [Finset.card_powersetCard, Finset.card_powersetCard, hs]`."
  have simpl : ∀ p ∈ Finset.antidiagonal n,
      (Finset.powersetCard p.1 s).card * (Finset.powersetCard p.2 s).card =
      Nat.choose n p.1 * Nat.choose n p.2 := by
    intro p _
    rw [Finset.card_powersetCard, Finset.card_powersetCard, hs]
  Hint "Apply the pointwise simplification to the whole sum."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl simpl]`."
  rw [Finset.sum_congr rfl simpl]
  Hint "The goal is now:
  `∑ p ∈ antidiagonal n, choose n p.1 * choose n p.2 = choose (2 * n) n`

  This is the Vandermonde identity `Nat.add_choose_eq n n n`,
  but the RHS has `2 * n` where Vandermonde gives `n + n`.
  Reshape first."
  Hint (hidden := true) "Try `have hh : 2 * n = n + n := by ring`."
  have hh : 2 * n = n + n := by ring
  Hint "Rewrite the goal to use `n + n`."
  Hint (hidden := true) "Try `rw [hh]`."
  rw [hh]
  Hint "The goal is
  `∑ p, choose n p.1 * choose n p.2 = (n + n).choose n`.

  Flip the equation and apply the Vandermonde identity."
  Hint (hidden := true) "Try `symm` then `exact Nat.add_choose_eq n n n`."
  symm
  exact Nat.add_choose_eq n n n

Conclusion "
Congratulations! You completed the **Combinatorics Problem Set**.

**Why this identity is natural**: The Vandermonde convolution
$\\binom{m+n}{k} = \\sum_{i+j=k} \\binom{m}{i} \\binom{n}{j}$
counts choosing $k$ elements from a group of $m + n$ by
partitioning: choose $i$ from the first $m$ and $j = k - i$ from
the second $n$. In our case $m = n = k$, so we are choosing $n$
people from two groups of $n$: pick $i$ from the first group and
$n - i$ from the second.

**A common false belief**: One might guess that
$\\binom{m+n}{k} = \\binom{m}{k} \\cdot \\binom{n}{k}$, but this
is wrong — the correct form is a **sum** of products
$\\sum \\binom{m}{i} \\binom{n}{k-i}$, not a single product. You
just proved why.

The result $\\binom{2n}{n}$ is the **central binomial coefficient**
— the largest entry in row $2n$ of Pascal's triangle. Concretely,
$\\binom{2n}{n}$ counts **lattice paths** from $(0,0)$ to $(n,n)$
using unit right and up steps: choose which $n$ of the $2n$ total
steps go right. It also appears in Catalan numbers and probability.

The proof integrates all four Phase 5 worlds: strip inside a sum
via `sum_congr rfl` (practiced in Level 11), reshape $2n = n + n$,
then apply Vandermonde. The strip-and-apply pattern, named in
Level 2 and used throughout, reaches its final form here —
stripping *inside* a sum via pointwise rewriting.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add
