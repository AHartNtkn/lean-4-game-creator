import Game.Metadata

World "Powerset"
Level 18

Title "Seeing PowersetCard: A Concrete Example"

Introduction "
# What Does PowersetCard Look Like?

Level 3 grounded `powerset` with a concrete computation. Now do the
same for `powersetCard`.

Consider the set $\\{1, 2, 3\\}$. Its 2-element subsets are:
- $\\{1, 2\\}$
- $\\{1, 3\\}$
- $\\{2, 3\\}$

That is 3 subsets, matching $\\binom{3}{2} = 3$.

**Your task**: Verify that `(Finset.powersetCard 2 ({1, 2, 3} : Finset ℕ)).card = 3`.
Lean can compute this directly.
"

/-- The number of 2-element subsets of {1, 2, 3} is 3. -/
Statement : (Finset.powersetCard 2 ({1, 2, 3} : Finset ℕ)).card = 3 := by
  Hint "Lean can compute the cardinality of a concrete powersetCard
  directly. Use `decide` to let Lean verify this by computation."
  Hint (hidden := true) "Try `decide`."
  decide

Conclusion "
One step: `decide`.

Lean computed the 2-element subsets of $\\{1, 2, 3\\}$:
- `powersetCard 2 {1, 2, 3} = {{1, 2}, {1, 3}, {2, 3}}`
- Count: 3 = 3. ✓

This matches $\\binom{3}{2} = 3$, which `card_powersetCard` (Level 17)
stated abstractly. Now you have seen both the abstract formula and the
concrete enumeration.

**Comparing `powerset` and `powersetCard`**:
- `powerset {1,2,3}` has $2^3 = 8$ elements (all subsets, any size)
- `powersetCard 2 {1,2,3}` has $\\binom{3}{2} = 3$ elements (only size-2 subsets)

The powerset is the union of all powersetCard layers:
$|\\mathcal{P}(s)| = \\sum_{k=0}^{n} |\\text{powersetCard}\\ k\\ s|
= \\sum_{k=0}^{n} \\binom{n}{k} = 2^n$
"

TheoremTab "Finset"

-- Enable decide for this concretization level only
DisabledTactic trivial native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
