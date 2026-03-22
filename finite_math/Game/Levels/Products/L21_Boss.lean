import Game.Metadata

World "Products"
Level 21

Title "Boss: Product Constructions"

Introduction "
# Boss: Three Arcs, One Proof

This world taught three product constructions:

1. **Cartesian product** (`s ×ˢ t`): membership via `mem_product`
   and `mk_mem_product`, cardinality via `card_product`
2. **Dependent product** (`s.sigma t`): membership via `mem_sigma`,
   cardinality via `card_sigma` and `sum_const`
3. **Diagonal decomposition**: `s ×ˢ s = s.diag ∪ s.offDiag`,
   with `diag_card`, `offDiag_card`, and `disjoint_diag_offDiag`

Prove all three claims below. `card_product` is disabled for
the third part — use the decomposition route.

**Hint**: Use `constructor` to split the conjunction into parts.
"

/-- Prove product membership, compute sigma cardinality, and compute
self-product cardinality via decomposition. -/
Statement (s : Finset ℕ) (a : ℕ) (ha : a ∈ s) (hs : s.card = 5) :
    (a, a) ∈ s ×ˢ s ∧ (s.sigma (fun _ => s)).card = 25 ∧ (s ×ˢ s).card = 25 := by
  Hint "The goal is a conjunction of three claims. Split it with
  `constructor` to handle each part separately."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Part 1: Product membership
  Hint "**Part 1**: Prove `(a, a) ∈ s ×ˢ s`. You have `ha : a ∈ s`
  — how do you build product membership from component memberships?"
  Hint (hidden := true) "Try `exact Finset.mk_mem_product ha ha`."
  · exact Finset.mk_mem_product ha ha
  Hint "Now split the remaining conjunction."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Part 2: Sigma cardinality
  Hint "**Part 2**: Compute `(s.sigma (fun _ => s)).card`. This is a
  constant-fiber sigma. What does `Finset.card_sigma` give you?"
  Hint (hidden := true) "Try `rw [Finset.card_sigma]`. This converts
  the sigma cardinality to a sum of fiber sizes."
  · rw [Finset.card_sigma]
    Hint "The fibers are all `s`, so the sum is constant. Use
    `Finset.sum_const` to simplify."
    Hint (hidden := true) "Try `rw [Finset.sum_const]`."
    rw [Finset.sum_const]
    Hint "Substitute `s.card = 5`. After substitution, for natural
    numbers scalar multiplication `•` is the same as ordinary
    multiplication `*`, so the goal closes."
    Hint (hidden := true) "Try `rw [hs]`."
    rw [hs]
    Hint (hidden := true) "The goal `5 • 5 = 25` is true by
    definition. Try `rfl`."
    rfl
  -- Part 3: Decomposition
  Hint "**Part 3**: Compute `(s ×ˢ s).card` without `card_product`.
  Use the decomposition route: split `s ×ˢ s` into diagonal and
  off-diagonal."
  Hint (hidden := true) "Try `rw [← Finset.diag_union_offDiag]`."
  · rw [← Finset.diag_union_offDiag]
    Hint "Apply `card_union_of_disjoint` with `disjoint_diag_offDiag`."
    Hint (hidden := true) "Try
    `rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]`."
    rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]
    Hint "Compute `s.diag.card` using `Finset.diag_card`."
    Hint (hidden := true) "Try `rw [Finset.diag_card]`."
    rw [Finset.diag_card]
    Hint "Compute `s.offDiag.card` using `Finset.offDiag_card`."
    Hint (hidden := true) "Try `rw [Finset.offDiag_card]`."
    rw [Finset.offDiag_card]
    Hint "Substitute `s.card = 5`."
    Hint (hidden := true) "Try `rw [hs]`."
    rw [hs]

Conclusion "
You integrated all three product construction arcs:

**Part 1 — Cartesian product membership**:
`mk_mem_product ha ha` builds `(a, a) ∈ s ×ˢ s` from `a ∈ s`.

**Part 2 — Sigma cardinality**:
`card_sigma` + `sum_const` computes the constant-fiber sigma:
$\\sum_{i \\in s} |s| = |s| \\cdot |s| = 25$.

**Part 3 — Diagonal decomposition**:
$$|s \\times^s s| = |s.\\text{diag}| + |s.\\text{offDiag}|
= 5 + (25 - 5) = 25$$

The **partition-then-count** strategy — decompose, verify
disjointness, count each piece, add — is a fundamental
technique you'll use whenever you need to count by cases.

**Looking ahead**: The product `Fin m × Fin n` is the index
set for entries of an $m \\times n$ matrix. Everything you've
learned here about counting and decomposing product pairs
applies directly to matrix entries in the Matrices world.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
DisabledTheorem Finset.card_product
