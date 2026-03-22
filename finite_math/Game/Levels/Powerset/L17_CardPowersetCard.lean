import Game.Metadata

World "Powerset"
Level 17

Title "Counting k-Element Subsets"

Introduction "
# C(n, k) Counts k-Element Subsets

How many 2-element subsets does a 5-element set have? The answer
is $\\binom{5}{2} = 10$. This is the **combinatorial meaning** of
the binomial coefficient that you proved identities for in the
BinomialCoefficients world.

The formal connection is:

`Finset.card_powersetCard : (powersetCard k s).card = Nat.choose s.card k`

The number of `k`-element subsets of `s` is exactly `Nat.choose (s.card) k`.

**Your task**: Apply `card_powersetCard` directly to state this
connection.
"

/-- `Finset.card_powersetCard` states that
`(powersetCard k s).card = Nat.choose s.card k`.

## Syntax
```
rw [Finset.card_powersetCard]
exact Finset.card_powersetCard k s
```

## When to use it
When you see `(powersetCard k s).card` and want to replace it
with `Nat.choose s.card k`, connecting subset counting to the
binomial coefficient.

## Meaning
The number of `k`-element subsets of an `n`-element set is
$\\binom{n}{k}$. This is *the* combinatorial interpretation of
`Nat.choose`.
-/
TheoremDoc Finset.card_powersetCard as "Finset.card_powersetCard" in "Finset"

/-- The number of k-element subsets equals choose(n, k). -/
Statement (s : Finset ℕ) :
    (Finset.powersetCard 2 s).card = Nat.choose s.card 2 := by
  Hint "The goal directly matches the statement of
  `Finset.card_powersetCard`. You can close it with `exact`."
  Hint (hidden := true) "Try `exact Finset.card_powersetCard 2 s`."
  exact Finset.card_powersetCard 2 s

Conclusion "
One step: `exact Finset.card_powersetCard 2 s`.

This is a **retrieval** level — you identified the right lemma
and applied it. The fact itself is profound:

$$|\\{t \\subseteq s \\mid |t| = k\\}| = \\binom{|s|}{k}$$

This is the standard combinatorial definition of 'n choose k':
the number of ways to choose `k` items from `n`.

In the BinomialCoefficients world, you proved identities about
`Nat.choose` purely from its recursive definition. Now you see
its **counting meaning**: `choose n k` counts the `k`-element
subsets of any `n`-element set.
"

NewTheorem Finset.card_powersetCard

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
