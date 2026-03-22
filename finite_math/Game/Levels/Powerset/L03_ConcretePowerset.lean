import Game.Metadata

World "Powerset"
Level 3

Title "Seeing the Powerset: A Concrete Example"

Introduction "
# What Does a Powerset Look Like?

Before diving deeper into abstract proofs, let's ground the powerset
in a concrete example.

Consider $s = \\{1, 2\\}$. Its powerset contains every possible
sub-collection:

| Subset | Size |
|:-:|:-:|
| $\\emptyset$ | 0 |
| $\\{1\\}$ | 1 |
| $\\{2\\}$ | 1 |
| $\\{1, 2\\}$ | 2 |

That's 4 subsets total — matching the formula $2^2 = 4$.

For each element, you independently choose *in* or *out*:
- Element 1: in or out (2 choices)
- Element 2: in or out (2 choices)
- Total: $2 \\times 2 = 4$ subsets

**Your task**: Verify that `({1, 2} : Finset Nat).powerset` has
exactly 4 elements. Lean can compute this directly.
"

/-- The powerset of {1, 2} has exactly 4 elements. -/
Statement : (({1, 2} : Finset ℕ).powerset).card = 4 := by
  Hint "Lean can compute the cardinality of a concrete finset's powerset
  directly. Use `decide` to let Lean verify this by computation."
  Hint (hidden := true) "Try `decide`."
  decide

Conclusion "
One step: `decide`.

For small concrete finsets, `decide` asks Lean to compute the answer
directly — it literally builds `({1, 2}).powerset`, counts its elements,
and checks the result equals 4.

**What `decide` computed**:
`({1, 2} : Finset Nat).powerset = {∅, {1}, {2}, {1, 2}}`
and `4 = 4`. ✓

In the rest of this world, you'll prove general facts about
powersets that work for *any* finset — not just `{1, 2}`. But
keeping this concrete picture in mind helps build intuition:
the powerset is the collection of *all possible sub-selections*.
"

TheoremTab "Finset"

-- Enable decide for this concretization level only
DisabledTactic trivial native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self
