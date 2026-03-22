import Game.Levels.Fintype.L01_MeetFintype
import Game.Levels.Fintype.L02_BoolIsFinite
import Game.Levels.Fintype.L03_ProductTypes
import Game.Levels.Fintype.L04_SumTypes
import Game.Levels.Fintype.L05_FunctionTypes
import Game.Levels.Fintype.L06_FinitenessMatters
import Game.Levels.Fintype.L07_CoachedPractice
import Game.Levels.Fintype.L08_SubtypeCounting
import Game.Levels.Fintype.L09_SubtypePractice
import Game.Levels.Fintype.L10_AbstractTypes
import Game.Levels.Fintype.L11_BijectiveCounting
import Game.Levels.Fintype.L12_CoachedBijection
import Game.Levels.Fintype.L13_ProducingEquiv
import Game.Levels.Fintype.L14_ConcreteComputation
import Game.Levels.Fintype.L15_Boss

World "Fintype"
Title "Fintype"

Introduction "
# Fintype: Counting Elements of Finite Types

You've spent several worlds counting elements of specific finsets —
using `card_insert`, `card_range`, `card_union`, and other `Finset.card`
lemmas. But there's a deeper question: how many elements does an entire
**type** have?

The answer is `Fintype` — a typeclass that says a type has finitely many
elements. When `α` has a `Fintype` instance, you get:
- `Fintype.card α` — the total number of elements
- `Finset.univ : Finset α` — the finset of ALL elements

## Why counting types matters

Counting the elements of a type is the foundation of combinatorics in
Lean. Once you know `Fintype.card α`, you can:
- **Apply pigeonhole**: if `card α > card β`, there is no injection `α → β`
- **Detect bijections**: if `card α = card β` and a map is injective,
  it must be surjective (and vice versa)
- **Classify finite structures**: two finite groups of the same prime
  order must be isomorphic

The `Fintype` typeclass makes all of this machine-checkable.

## The composition rules

The power of `Fintype` is **composition**: if you know the cardinalities
of building blocks, you can compute the cardinality of anything built
from them:

| Construction | Formula | Name |
|---|---|---|
| `α × β` (product) | `card α * card β` | Multiplication principle |
| `α ⊕ β` (sum) | `card α + card β` | Addition principle |
| `α → β` (functions) | `card β ^ card α` | Exponentiation principle |
| `{ x // ¬P x }` (subtype) | `card α - card P` | Complement counting |
| `α ≃ β` (equivalence) | `card α = card β` | Bijective counting |

**Warning**: Not every type is finite! The natural numbers `ℕ` have no
`Fintype` instance. `Fintype.card ℕ` would be a type error. Finiteness
is a property that must be established, not assumed.
"
