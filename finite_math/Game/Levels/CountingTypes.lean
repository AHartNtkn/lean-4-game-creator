import Game.Levels.CountingTypes.L01_BinaryStrings
import Game.Levels.CountingTypes.L02_EquivWarmUp
import Game.Levels.CountingTypes.L03_LabelingAGrid
import Game.Levels.CountingTypes.L04_FunctionsFromASum
import Game.Levels.CountingTypes.L05_FallingFactorials
import Game.Levels.CountingTypes.L06_FallingFactorialIdentity
import Game.Levels.CountingTypes.L07_FactorialConnection
import Game.Levels.CountingTypes.L08_CountingInjections
import Game.Levels.CountingTypes.L09_InjectionPractice
import Game.Levels.CountingTypes.L10_TheGap
import Game.Levels.CountingTypes.L11_Boss

World "CountingTypes"
Title "Counting Types"

Introduction "
# Counting Types: Concrete Computations

You've mastered the composition rules for `Fintype.card`:

| Principle | Lemma | Formula |
|---|---|---|
| Base (Fin) | `card_fin` | `card (Fin n) = n` |
| Base (Bool) | `card_bool` | `card Bool = 2` |
| Multiplication | `card_prod` | `card (α × β) = card α * card β` |
| Addition | `card_sum` | `card (α ⊕ β) = card α + card β` |
| Exponentiation | `card_fun` | `card (α → β) = card β ^ card α` |
| Equivalence | `card_congr` | `α ≃ β → card α = card β` |

In this world, you'll apply these abstract rules to **concrete finite
types** and see what the numbers mean:

- **Binary strings**: `Fin n → Bool` has $2^n$ elements — the subsets
  of an `n`-element set
- **Equivalence in action**: use `card_congr` to resolve abstract domains
- **Grid labelings**: `Fin m × Fin n → Bool` labels cells of a grid
- **Functions from sums**: `Fin m ⊕ Fin n → Bool` splits into two
  independent function types
- **Falling factorials**: `Nat.descFactorial` counts ordered selections
  without replacement, interpolating between $n^k$ and $n!$
- **Counting injections**: `card_embedding_eq` connects embeddings
  `α ↪ β` to the falling factorial
- **The gap**: the difference $n^k - n^{\\underline{k}}$ counts
  non-injective functions — computed via the *dual-have + omega*
  strategy

The boss integrates all these skills: computing both the function count
and injection count for a composite type, then taking their difference.
"
