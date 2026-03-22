import Game.Metadata

World "Powerset"
Level 15

Title "Subsets of a Given Size"

Introduction "
# PowersetCard: Subsets of Size k

The full powerset contains *all* subsets. But often you want just
the subsets of a specific size: the 2-element subsets, the 3-element
subsets, etc.

`Finset.powersetCard k s` is the finset of all subsets of `s` that
have exactly `k` elements.

The membership characterization is:

`Finset.mem_powersetCard : t ∈ powersetCard k s ↔ t ⊆ s ∧ t.card = k`

So `t` is in `powersetCard k s` exactly when `t` is a subset of `s`
**and** has cardinality `k`. Two conditions — a conjunction.

**Your task**: Given `hsub : s ⊆ t` and `hcard : s.card = 2`, prove
that `s ∈ powersetCard 2 t`.
"

/-- `Finset.powersetCard k s` is the finset of all `k`-element subsets of `s`.

## Type
`Finset.powersetCard : ℕ → Finset α → Finset (Finset α)`

## Key characterization
`Finset.mem_powersetCard : t ∈ powersetCard k s ↔ t ⊆ s ∧ t.card = k`

## Cardinality
`Finset.card_powersetCard : (powersetCard k s).card = Nat.choose s.card k`

The number of `k`-element subsets of an `n`-element set is $\binom{n}{k}$.

## Example
The 2-element subsets of `{1, 2, 3}` are `{1,2}`, `{1,3}`, `{2,3}` —
three subsets, matching $\binom{3}{2} = 3$.
-/
DefinitionDoc Finset.powersetCard as "Finset.powersetCard"

/-- `Finset.mem_powersetCard` states that
`t ∈ powersetCard k s ↔ t ⊆ s ∧ t.card = k`.

## Syntax
```
rw [Finset.mem_powersetCard]     -- in the goal
rw [Finset.mem_powersetCard] at h -- in a hypothesis
```

## When to use it
When you see `t ∈ powersetCard k s` and want to split it into two
conditions: `t ⊆ s` and `t.card = k`.

## After rewriting
The goal becomes a conjunction. Use `constructor` to split it into
two subgoals, then prove each separately.
-/
TheoremDoc Finset.mem_powersetCard as "Finset.mem_powersetCard" in "Finset"

/-- A 2-element subset of t is in powersetCard 2 t. -/
Statement (s t : Finset ℕ) (hsub : s ⊆ t) (hcard : s.card = 2) :
    s ∈ Finset.powersetCard 2 t := by
  Hint "The goal is `s ∈ powersetCard 2 t`. Rewrite with
  `Finset.mem_powersetCard` to split into two conditions."
  Hint (hidden := true) "Try `rw [Finset.mem_powersetCard]`."
  rw [Finset.mem_powersetCard]
  Hint "The goal is now `s ⊆ t ∧ s.card = 2` — a conjunction.
  Split it with `constructor`."
  Hint (hidden := true) "Try `constructor`."
  constructor
  · Hint "**Left goal**: `s ⊆ t`. This is your hypothesis `hsub`."
    Hint (hidden := true) "Try `exact hsub`."
    exact hsub
  · Hint "**Right goal**: `s.card = 2`. This is your hypothesis `hcard`."
    Hint (hidden := true) "Try `exact hcard`."
    exact hcard

Conclusion "
You proved `s ∈ powersetCard 2 t` by:
1. `rw [mem_powersetCard]` — convert to `s ⊆ t ∧ s.card = 2`
2. `constructor` — split into two subgoals
3. `exact hsub` and `exact hcard` — close each from hypotheses

**Pattern**: `mem_powersetCard` always produces a conjunction.
After rewriting, expect to use `constructor` to split it.

Compare with `mem_powerset`: powerset membership gives one condition
(subset), while powersetCard membership gives two (subset AND card).
"

NewDefinition Finset.powersetCard
NewTheorem Finset.mem_powersetCard

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
