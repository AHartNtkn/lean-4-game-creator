import Game.Levels.BigOpIntro.L01_SumEmpty
import Game.Levels.BigOpIntro.L02_SumSingleton
import Game.Levels.BigOpIntro.L03_SumInsert
import Game.Levels.BigOpIntro.L04_TwoElementSum
import Game.Levels.BigOpIntro.L05_ThreeElementSum
import Game.Levels.BigOpIntro.L06_ProdEmpty
import Game.Levels.BigOpIntro.L07_ProdTwoElement
import Game.Levels.BigOpIntro.L08_SumCongr
import Game.Levels.BigOpIntro.L09_BaseCaseContrast
import Game.Levels.BigOpIntro.L10_CardAsSum
import Game.Levels.BigOpIntro.L11_CardSumPractice
import Game.Levels.BigOpIntro.L12_MultisetConnection
import Game.Levels.BigOpIntro.L13_ProdCongr
import Game.Levels.BigOpIntro.L14_ProdIntegration
import Game.Levels.BigOpIntro.L15_Boss

World "BigOpIntro"
Title "Big Operators: Introduction"

Introduction "
# Big Operators: ∑ and ∏

In ordinary mathematics, you write $\\sum_{x \\in S} f(x)$ to sum a
function over a set. In Lean, this is `∑ x ∈ s, f x` — called a
**big operator** because it operates over an entire finset at once.

This world introduces the core big-operator vocabulary:
- **Empty**: `∑ x ∈ ∅, f x = 0` and `∏ x ∈ ∅, f x = 1`
- **Singleton**: `∑ x ∈ {a}, f x = f a`
- **Insert**: `∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x` (when `a ∉ s`)
- **Congruence**: rewriting the function inside a sum or product
- **Cardinality bridge**: `s.card = ∑ x ∈ s, 1`
- **Abstraction ladder**: how `Finset.sum` reduces through Multiset

Together, these let you unfold any sum over a concrete finset into
individual terms — the big-operator analogue of the insert-peel
pattern you already know from finset membership.

**Prerequisites**: You should be comfortable with finset membership
(`mem_insert`, `mem_singleton`), the `insert` construction, and
proving non-membership with `omega`.
"
