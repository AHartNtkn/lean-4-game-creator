import Game.Metadata

World "Powerset"
Level 21

Title "Singleton Subsets: Choose 1"

Introduction "
# Each Element Gives One Singleton Subset

How many 1-element subsets does a set have? Exactly as many as it
has elements: each element $a$ gives the singleton subset $\\{a\\}$.

In Lean terms: `(powersetCard 1 s).card = s.card`.

This follows from two facts you already know:
- `card_powersetCard`: the count is `Nat.choose s.card 1`
- `Nat.choose_one_right`: `Nat.choose n 1 = n`

**Your task**: Chain these two rewrites to prove the result.
"

/-- The number of 1-element subsets of s equals s.card. -/
Statement (s : Finset ℕ) :
    (Finset.powersetCard 1 s).card = s.card := by
  Hint "Start by converting the powersetCard cardinality to a
  binomial coefficient using `Finset.card_powersetCard`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard]`."
  rw [Finset.card_powersetCard]
  Hint "The goal is `Nat.choose s.card 1 = s.card`.
  From the BinomialCoefficients world, you know that choosing
  1 from `n` gives `n`. Use `Nat.choose_one_right`."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right]`."
  rw [Nat.choose_one_right]

Conclusion "
Two rewrites: `card_powersetCard` then `choose_one_right`.

This connects the **set-theoretic** fact (each element gives one
singleton subset) to the **combinatorial** fact ($\\binom{n}{1} = n$).

**Cross-world connection**: In the BinomialCoefficients world,
`choose_one_right` was a purely algebraic fact about the recursive
definition. Now you see its counting meaning: choosing 1 item from
$n$ items can be done in $n$ ways.

This is the k=1 case of the general pattern:
$$|\\text{powersetCard}\\ k\\ s| = \\binom{|s|}{k}$$
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
