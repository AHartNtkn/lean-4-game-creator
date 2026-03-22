import Game.Metadata

World "Powerset"
Level 22

Title "The Full Set: Choose n"

Introduction "
# The k=n Boundary

Level 19 showed $\\binom{n}{0} = 1$: only the empty set has 0 elements.
Level 21 showed $\\binom{n}{1} = n$: each element gives one singleton.

Now complete the boundary trio with $\\binom{n}{n} = 1$: the only
$n$-element subset of an $n$-element set is the set itself.

**Your task**: Prove `(Finset.powersetCard s.card s).card = 1`.

This follows the same two-rewrite pattern as Levels 19 and 21:
- `card_powersetCard` to convert to `Nat.choose`
- `Nat.choose_self` to simplify $\\binom{n}{n} = 1$
"

/-- Every finset has exactly one subset of the same size: itself. -/
Statement (s : Finset ℕ) :
    (Finset.powersetCard s.card s).card = 1 := by
  Hint "Convert the powersetCard cardinality to a binomial
  coefficient using `Finset.card_powersetCard`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard]`."
  rw [Finset.card_powersetCard]
  Hint "The goal is `Nat.choose s.card s.card = 1`. From the
  BinomialCoefficients world, `Nat.choose_self` says
  `Nat.choose n n = 1`."
  Hint (hidden := true) "Try `rw [Nat.choose_self]`."
  rw [Nat.choose_self]

Conclusion "
Two rewrites: `card_powersetCard` then `choose_self`.

The only $n$-element subset of an $n$-element set is the set itself.
This gives the boundary value $\\binom{n}{n} = 1$.

**Boundary trio complete**:
| $k$ | $\\binom{n}{k}$ | Meaning |
|:-:|:-:|:--|
| 0 | 1 | Only `∅` has 0 elements (Level 19) |
| 1 | $n$ | Each element gives one singleton (Level 21) |
| $n$ | 1 | Only `s` itself has $n$ elements (this level) |

These three anchor points — the two endpoints and the linear case —
ground the general formula $\\binom{n}{k}$ in concrete intuition.

**Symmetry connection**: Notice that $\\binom{n}{0} = \\binom{n}{n} = 1$.
This is an instance of the symmetry $\\binom{n}{k} = \\binom{n}{n-k}$
that the boss will use.

**The powerset decomposes by size**: The powerset of $s$ is the
disjoint union of the sets `powersetCard 0 s`, `powersetCard 1 s`,
..., `powersetCard n s` — one layer for each possible subset size.
Adding up the sizes of these layers gives:

$$\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$$

This connects `card_powerset` (Level 12: $2^n$ total subsets) to
`card_powersetCard` (Level 17: $\\binom{n}{k}$ subsets of size $k$).
The total count $2^n$ is the sum of the layer counts. You will
prove this identity formally in the BinomialTheorem world.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
