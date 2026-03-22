import Game.Metadata

World "Powerset"
Level 19

Title "Zero-Element Subsets: Choose 0"

Introduction "
# The k=0 Boundary

How many 0-element subsets does any set have? Exactly one: the
empty set `∅`. This gives $\\binom{n}{0} = 1$ for all $n$.

Together with the k=1 case (Level 21: $\\binom{n}{1} = n$), this
grounds the binomial coefficient at its two simplest boundary values.

**Your task**: Prove `(Finset.powersetCard 0 s).card = 1`.

Chain `card_powersetCard` with `Nat.choose_zero_right` (from
BinomialCoefficients).
"

/-- Every finset has exactly one 0-element subset. -/
Statement (s : Finset ℕ) :
    (Finset.powersetCard 0 s).card = 1 := by
  Hint "Convert the powersetCard cardinality to a binomial
  coefficient using `Finset.card_powersetCard`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard]`."
  rw [Finset.card_powersetCard]
  Hint "The goal is `Nat.choose s.card 0 = 1`. From the
  BinomialCoefficients world, `Nat.choose_zero_right` says
  `Nat.choose n 0 = 1` for all `n`."
  Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
  rw [Nat.choose_zero_right]

Conclusion "
Two rewrites: `card_powersetCard` then `choose_zero_right`.

The only 0-element subset of any set is `∅`. This gives the
boundary value $\\binom{n}{0} = 1$.

**Boundary cases of choose**:
| $k$ | $\\binom{n}{k}$ | Meaning |
|:-:|:-:|:--|
| 0 | 1 | Only `∅` has 0 elements (this level) |
| 1 | $n$ | Each element gives one singleton (Level 21) |
| $n$ | 1 | Only `s` itself has $n$ elements (Level 22) |

These three anchor points help build intuition for the general
formula before encountering it in complex proofs.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
