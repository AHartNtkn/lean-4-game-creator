import Game.Metadata

World "Powerset"
Level 23

Title "Too Many Elements: The k > n Boundary"

Introduction "
# When k Exceeds the Set Size

Levels 19-22 covered the boundary cases $k = 0$, $k = 1$, and
$k = n$. Now consider the fourth boundary: what happens when
$k > n$?

If you want more elements than the set has, there are no such
subsets. The answer is zero: $\\binom{n}{k} = 0$ when $k > n$.

This makes intuitive sense: you can't choose 5 toppings from
a menu of 3. There are zero ways to do that.

**Your task**: Given `hk : s.card < k`, prove that
`(Finset.powersetCard k s).card = 0`.

Chain `card_powersetCard` with `Nat.choose_eq_zero_of_lt`
(from BinomialCoefficients).
"

/-- There are no k-element subsets when k exceeds the set size. -/
Statement (s : Finset ℕ) (k : ℕ) (hk : s.card < k) :
    (Finset.powersetCard k s).card = 0 := by
  Hint "Convert the powersetCard cardinality to a binomial
  coefficient using `Finset.card_powersetCard`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard]`."
  rw [Finset.card_powersetCard]
  Hint "The goal is `Nat.choose s.card k = 0`. From the
  BinomialCoefficients world, `Nat.choose_eq_zero_of_lt` says
  that `Nat.choose n k = 0` when `n < k`."
  Hint (hidden := true) "Try `exact Nat.choose_eq_zero_of_lt hk`."
  exact Nat.choose_eq_zero_of_lt hk

Conclusion "
Two steps: `card_powersetCard` then `choose_eq_zero_of_lt`.

**Boundary quartet complete**:
| $k$ | $\\binom{n}{k}$ | Meaning |
|:-:|:-:|:--|
| 0 | 1 | Only `∅` has 0 elements (Level 19) |
| 1 | $n$ | Each element gives one singleton (Level 21) |
| $n$ | 1 | Only `s` itself has $n$ elements (Level 22) |
| $> n$ | 0 | Can't choose more than available (this level) |

The four boundary cases give a complete picture of the binomial
coefficient's behavior at its extremes. Everything in between
is captured by Pascal's identity and the general formula.

**Symmetry connection**: The k=0 and k=n cases both give 1.
The k > n case gives 0. These boundary behaviors are consistent
with the symmetry $\\binom{n}{k} = \\binom{n}{n-k}$: when $k > n$,
$n - k$ would be negative, so the symmetric case doesn't exist.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
