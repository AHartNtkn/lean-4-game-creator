import Game.Levels.Finsupp.L01_SingleEqSame
import Game.Levels.Finsupp.L02_SingleEqOfNe
import Game.Levels.Finsupp.L03_SupportSingle
import Game.Levels.Finsupp.L04_SingleZero
import Game.Levels.Finsupp.L05_MemSupportIff
import Game.Levels.Finsupp.L06_MemSupportIffReverse
import Game.Levels.Finsupp.L07_SingleApply
import Game.Levels.Finsupp.L08_PointwiseAddition
import Game.Levels.Finsupp.L09_Accumulation
import Game.Levels.Finsupp.L10_SingleAddAlgebra
import Game.Levels.Finsupp.L11_Cancellation
import Game.Levels.Finsupp.L12_SingleAddIntegration
import Game.Levels.Finsupp.L13_Extensionality
import Game.Levels.Finsupp.L14_SupportOfSum
import Game.Levels.Finsupp.L15_SummingOverSupport
import Game.Levels.Finsupp.L16_SupportCoaching
import Game.Levels.Finsupp.L17_Boss

World "Finsupp"
Title "Finsupp"

Introduction "
# Finitely Supported Functions

In previous worlds, you worked with `Finset` — finite collections of
elements. Now we turn to **finitely supported functions**: functions
`f : α → M` where `f a ≠ 0` for only finitely many values of `a`.

In Lean, a finitely supported function from `α` to `M` (where `M`
has a zero) is bundled as `Finsupp α M`, written `α →₀ M`. The
key data is:
- A function `α → M` giving the value at each point
- A `Finset α` called the **support**, recording where the function
  is nonzero
- A proof that `a ∈ support ↔ f a ≠ 0`

The simplest way to build a `Finsupp` is `Finsupp.single a b` — the
function that is `b` at `a` and `0` everywhere else. Think of it
as a spike at position `a` with height `b`.

Finitely supported functions appear throughout mathematics:
- A **polynomial** is a finitely supported function from `ℕ` to its
  coefficient ring (most coefficients are zero)
- A **formal sum** of group elements is a finitely supported function
  from the group to `ℤ`
- A **vector** relative to a basis is a finitely supported function
  from the basis set to the scalar field

In this world you will learn to:
1. Construct finitely supported functions using `single`
2. Evaluate them at points (at the support, and away from it)
3. Reason about their `support` as a `Finset`
4. Add them pointwise — including accumulation at shared positions
5. Combine singles algebraically using `single_add`
6. Prove equality using extensionality
7. Bound the support of a sum using `support_add`
8. Connect Finsupp back to big operators via summation over supports

This is a focused introduction to `Finsupp`. Operations like
`Finsupp.mapDomain` (reindexing by a function on the domain) are
not covered here.
"
