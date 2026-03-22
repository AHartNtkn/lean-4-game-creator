import Game.Metadata

World "Powerset"
Level 27

Title "Boss: Subset Symmetry"

Introduction "
# Boss: Counting Complements

Given a powerset member `t`, its cardinality is bounded by the set
size. This bound is the key to the symmetry identity: the number of
`t.card`-element subsets equals the number of `(n - t.card)`-element
subsets.

Prove the formal version:

$$|\\text{powersetCard}\\ (\\text{t.card})\\ s| + |\\text{powersetCard}\\ (n - \\text{t.card})\\ s| = 2 \\cdot \\binom{n}{\\text{t.card}}$$

**What you need** (all from this world and prior worlds):
- `rw [Finset.mem_powerset] at ...` — extract `t ⊆ s` (Level 5)
- `Finset.card_le_card` — bound `t.card` by `s.card` (Level 24)
- `rw [hs] at ...` — substitute card value
- `Finset.card_powersetCard` — convert subset counts to `choose` (Level 17)
- `Nat.choose_symm ...` — the binomial symmetry (Level 26)
- `ring` — close the arithmetic (BigOpAlgebra)
"

/-- `omega` solves linear arithmetic goals over natural numbers
and integers. It handles equalities, inequalities, and
combinations of both.

## When to use it
When the goal is a linear arithmetic statement like
`a + b ≤ c + d` or `n = m + 1`.
-/
TacticDoc omega

/-- The count of t.card-element and (n - t.card)-element subsets is
twice the binomial coefficient. -/
Statement (n : ℕ) (s t : Finset ℕ) (ht : t ∈ s.powerset) (hs : s.card = n) :
    (Finset.powersetCard t.card s).card
    + (Finset.powersetCard (n - t.card) s).card
    = 2 * Nat.choose n t.card := by
  Hint "First, extract the subset fact from `ht`. This is the Level 5
  pattern: rewrite `mem_powerset` in a hypothesis."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at ht`."
  rw [Finset.mem_powerset] at ht
  Hint "Now `ht : t ⊆ s`. Derive the cardinality bound: subsets can't
  be bigger than the parent set. Use `Finset.card_le_card` (Level 24)."
  Hint (hidden := true) "Try `have hle := Finset.card_le_card ht`."
  have hle := Finset.card_le_card ht
  Hint "Now `hle : t.card ≤ s.card`. Substitute `s.card` with `n`
  using `hs` so the bound matches what `choose_symm` needs."
  Hint (hidden := true) "Try `rw [hs] at hle`."
  rw [hs] at hle
  Hint "Now convert the first `powersetCard` cardinality to a
  binomial coefficient."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard]`."
  rw [Finset.card_powersetCard]
  Hint "Do the same for the second `powersetCard` term."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard]`."
  rw [Finset.card_powersetCard]
  Hint "Substitute `s.card` with `n`."
  Hint (hidden := true) "Try `rw [hs]`."
  rw [hs]
  Hint "The goal is `choose n t.card + choose n (n - t.card) = 2 * choose n t.card`.
  Use `Nat.choose_symm hle` to rewrite `choose n (n - t.card)` to
  `choose n t.card`. This is the Level 26 pattern."
  Hint (hidden := true) "Try `rw [Nat.choose_symm hle]`."
  rw [Nat.choose_symm hle]
  Hint "The goal is `choose n t.card + choose n t.card = 2 * choose n t.card`.
  This is $x + x = 2x$. Close with `ring`."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
Congratulations! You proved the symmetry identity for powersetCard,
integrating skills from across the entire world:

**Skills from the membership branch (Levels 1-11)**:
- `rw [mem_powerset] at ht` — extracting a subset from powerset membership
- `Finset.card_le_card ht` — bounding cardinality via subset

**Skills from the counting branch (Levels 12-25)**:
- `Finset.card_powersetCard` — converting subset counts to `choose`
- `rw [hs]` — substituting a known card value

**Skills from BinomialCoefficients and Level 26**:
- `Nat.choose_symm hle` — rewriting with a proof argument
- `ring` — closing arithmetic

**The mathematical insight**: The proof required extracting `t ⊆ s`
from `t ∈ s.powerset` — not because we need to know anything about
`t` specifically, but because we need the *bound* `t.card ≤ n` to
justify the symmetry identity. The membership branch provides the
inequality that the counting branch consumes.

**Why complement symmetry holds**: Choosing which `t.card` elements
to *include* in a subset is the same as choosing which `n - t.card`
elements to *exclude*. This bijection between a subset and its
complement is why $\\binom{n}{k} = \\binom{n}{n-k}$.

**Looking ahead**: The powerset of $s$ decomposes into layers by
size. Summing $\\binom{n}{k}$ over all $k$ from $0$ to $n$ gives
$2^n$ — connecting `card_powerset` to `card_powersetCard`. You'll
prove this identity formally in the BinomialTheorem world.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith omega
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
