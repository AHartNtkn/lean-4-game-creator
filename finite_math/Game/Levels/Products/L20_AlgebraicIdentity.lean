import Game.Metadata

World "Products"
Level 20

Title "The Algebraic Identity"

Introduction "
# From Structure to Algebra

In the previous level you proved the *structural* decomposition:

$$(s \\times^s s).\\text{card} = s.\\text{diag}.\\text{card} + s.\\text{offDiag}.\\text{card}$$

Now let's cash in the structural result for an *algebraic*
identity. You know:

- `Finset.diag_card`: $|s.\\text{diag}| = |s|$
- `Finset.offDiag_card`: $|s.\\text{offDiag}| = |s|^2 - |s|$

Substituting these into the decomposition gives:

$$|s \\times^s s| = |s| + (|s|^2 - |s|)$$

This is the general identity $n^2 = n + (n^2 - n)$, proved
not by algebra but by **counting two ways**: the left side
counts all pairs, the right side counts same-element pairs
plus distinct-element pairs.

**Your task**: Prove this algebraic identity for any finset `s`.
"

/-- The self-product cardinality equals diagonal count plus off-diagonal count in algebraic form. -/
Statement (s : Finset ℕ) :
    (s ×ˢ s).card = s.card + (s.card * s.card - s.card) := by
  Hint "Start the same way as the structural decomposition:
  replace `s ×ˢ s` with `s.diag ∪ s.offDiag`."
  Hint (hidden := true) "Try `rw [← Finset.diag_union_offDiag]`."
  rw [← Finset.diag_union_offDiag]
  Hint "Split the union cardinality using disjointness."
  Hint (hidden := true) "Try
  `rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]`."
  rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]
  Hint "Now substitute the diagonal cardinality using `Finset.diag_card`."
  Hint (hidden := true) "Try `rw [Finset.diag_card]`."
  rw [Finset.diag_card]
  Hint "Substitute the off-diagonal cardinality using `Finset.offDiag_card`."
  Hint (hidden := true) "Try `rw [Finset.offDiag_card]`."
  rw [Finset.offDiag_card]

Conclusion "
You've derived the **general algebraic identity**:

$$|s \\times^s s| = |s| + (|s|^2 - |s|)$$

This is the mathematical punchline of the decomposition arc.
The identity $n^2 = n + n(n-1)$ isn't just algebraic
manipulation — it reflects a *structural fact*: every pair
from $s$ is either a same-element pair (there are $n$ of
those) or a distinct-element pair (there are $n^2 - n$ of
those).

This is an example of a **combinatorial proof of an algebraic
identity**: instead of manipulating symbols, you count the
same set two different ways. The decomposition route
(diagonal + off-diagonal) and the direct route (`card_product`)
both count $|s \\times^s s|$, and equating them gives the
identity.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
