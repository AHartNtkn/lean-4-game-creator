import Game.Metadata

World "Powerset"
Level 20

Title "The Unique Zero-Element Subset"

Introduction "
# What Is the Only 0-Element Subset?

Level 19 proved that there is exactly one 0-element subset of any
set: $(\\text{powersetCard}\\ 0\\ s).\\text{card} = 1$.

But *which* subset is it? The empty set `∅`, of course — it is the
only set with zero elements. The formal statement is:

`Finset.powersetCard_zero : powersetCard 0 s = {∅}`

This identifies the unique element (not just counts to 1). The
distinction matters: *counting* tells you 'there is exactly one,'
while *identifying* tells you 'and it is `∅`.'

**Your task**: Prove `Finset.powersetCard 0 s = {∅}`.

This is a retrieval level: find the right lemma and apply it.
"

/-- `Finset.powersetCard_zero` states `powersetCard 0 s = {∅}`.

## Syntax
```
exact Finset.powersetCard_zero s
```

## When to use it
When the goal involves `powersetCard 0 s` and you want to replace
it with the singleton `{∅}`. This is stronger than knowing the
count is 1 — it identifies the unique element.

## Relationship to card_powersetCard
`card_powersetCard` gives `(powersetCard 0 s).card = choose n 0 = 1`.
`powersetCard_zero` gives the stronger statement: the set itself is `{∅}`.
-/
TheoremDoc Finset.powersetCard_zero as "Finset.powersetCard_zero" in "Finset"

/-- The only 0-element subset of any finset is the empty set. -/
Statement (s : Finset ℕ) : Finset.powersetCard 0 s = {∅} := by
  Hint "The Mathlib lemma `Finset.powersetCard_zero` states this
  directly. Apply it."
  Hint (hidden := true) "Try `exact Finset.powersetCard_zero s`."
  exact Finset.powersetCard_zero s

Conclusion "
One step: `exact Finset.powersetCard_zero s`.

Level 19 told you *how many* 0-element subsets there are (one).
This level tells you *which one* it is (`∅`).

This distinction between counting and identifying recurs throughout
combinatorics:
- $\\binom{n}{0} = 1$ (count) vs `powersetCard 0 s = {∅}` (identity)
- $\\binom{n}{n} = 1$ (count) vs 'the only $n$-element subset is $s$ itself' (identity)

The counting facts are what the boss needs for arithmetic. The
identification facts are what you need for understanding *why*
the arithmetic works.
"

NewTheorem Finset.powersetCard_zero

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
