import Game.Levels.Products.L01_ProductMembership
import Game.Levels.Products.L02_MkMemProduct
import Game.Levels.Products.L03_ExtractFromProduct
import Game.Levels.Products.L04_ProductSubset
import Game.Levels.Products.L05_ProductCardIntegration
import Game.Levels.Products.L06_SigmaIntro
import Game.Levels.Products.L07_ConcreteSigma
import Game.Levels.Products.L08_ConcreteSigmaFormula
import Game.Levels.Products.L09_SigmaCardinality
import Game.Levels.Products.L10_SigmaRecovery
import Game.Levels.Products.L11_Diagonal
import Game.Levels.Products.L12_OffDiagonal
import Game.Levels.Products.L13_OffDiagExtraction
import Game.Levels.Products.L14_DiagCard
import Game.Levels.Products.L15_OffDiagCard
import Game.Levels.Products.L16_OffDiagBinomial
import Game.Levels.Products.L17_DecompositionReverse
import Game.Levels.Products.L18_DisjointnessCoaching
import Game.Levels.Products.L19_GeneralDecomposition
import Game.Levels.Products.L20_AlgebraicIdentity
import Game.Levels.Products.L21_Boss

World "Products"
Title "Products"

Introduction "
# Product Constructions

You've already used `s ×ˢ t` and `card_product` in the Cardinality
world. This world goes deeper into the **product construction**
family — the tools for building and reasoning about pairs drawn
from finsets.

**Cartesian product** `s ×ˢ t`:
The set of all pairs `(a, b)` with `a ∈ s` and `b ∈ t`. You know
its cardinality. Now you'll learn to characterize its membership
with `mem_product`, build pairs with `mk_mem_product`, and extract
component memberships.

**Dependent product** `s.sigma t`:
A generalization where the set of valid second components depends
on which first component was chosen. Its cardinality is a sum
rather than a product: $|s.\\text{sigma}\\ t| = \\sum_{i \\in s} |t\\,i|$.

**Diagonal** `s.diag` and **off-diagonal** `s.offDiag`:
The self-product `s ×ˢ s` splits into pairs where coordinates
agree (diagonal) and pairs where they differ (off-diagonal).
This decomposition is a fundamental technique for counting
pairs of elements.

**The proof toolkit**:
- `Finset.mem_product`: `p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t`
- `Finset.mk_mem_product`: `a ∈ s → b ∈ t → (a, b) ∈ s ×ˢ t`
- `Finset.mem_sigma`: `a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1`
- `Finset.card_sigma`: `(s.sigma t).card = ∑ a ∈ s, (t a).card`
- `Finset.mem_diag`: `x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2`
- `Finset.mem_offDiag`: `x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2`
- `Finset.diag_union_offDiag`: `s.diag ∪ s.offDiag = s ×ˢ s`

These are the finset-level tools for reasoning about tuples, pairs,
and multi-dimensional counting.
"
