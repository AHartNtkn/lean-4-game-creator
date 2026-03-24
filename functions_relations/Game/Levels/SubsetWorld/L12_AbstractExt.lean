import Game.Metadata

World "SubsetWorld"
Level 12

Title "Abstract Set Equality"

Introduction "
# Ext Without Arithmetic

In Levels 10 and 11, both set equalities used arithmetic predicates,
and `omega` closed each direction. But `ext` is not about arithmetic —
it is about **logic**. The closing move depends on the predicates
involved, not on `omega`.

**Your task**: Given a hypothesis `h : ∀ x, p x ↔ q x`, prove that
`{x | p x} = {x | q x}`.

No arithmetic. No `omega`. The proof uses only the hypothesis `h`
and the logical structure of `ext` + `constructor`.

**Proof plan**:
1. `ext x` — reduce to membership biconditional
2. `constructor` — split the `↔`
3. **Forward**: the hypothesis `h x` gives `p x → q x` (its `.1`)
4. **Backward**: `h x` also gives `q x → p x` (its `.2`)

Or: after `ext x`, notice that the goal IS `p x ↔ q x`, which is
exactly `h x`. So `exact h x` closes the goal in one step!
"

/-- If two predicates are pointwise equivalent, the corresponding
sets are equal. -/
Statement (α : Type) (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    {x : α | p x} = {x : α | q x} := by
  Hint "Use `ext x` to reduce to a membership biconditional."
  ext x
  Hint "The goal is `x ∈ ..x | p x.. ↔ x ∈ ..x | q x..`, which
  unfolds to `p x ↔ q x`. The hypothesis `h` gives exactly this
  for any `x`. Use `exact h x` to close the goal directly.

  Alternatively, use `constructor` and prove each direction using
  `(h x).1` and `(h x).2`."
  Hint (hidden := true) "`exact h x` closes the goal in one step.

  Or: `constructor` then `· intro hpx; exact (h x).1 hpx`
  then `· intro hqx; exact (h x).2 hqx`."
  Branch
    constructor
    · intro hpx
      exact (h x).1 hpx
    · intro hqx
      exact (h x).2 hqx
  exact h x

Conclusion "
You proved a set equality without any arithmetic. The key insight:
after `ext x`, the goal was `p x ↔ q x`, and the hypothesis `h x`
provided exactly that.

**The closing move depends on the predicates**: In Level 10, the
closing move was `omega` (bridging `n < 3` and `n < 5`). In Level 11,
it was also `omega` (bridging `n ≤ 2` and `n < 3`). Here, the closing
move was `exact h x` — pure hypothesis application.

This illustrates a general principle: `ext x; constructor` gives you
the STRUCTURE of a set equality proof, but the CLOSING MOVE depends
on what the set-builder predicates actually say. For arithmetic
predicates, you close with `omega`. For abstract predicates, you
close with hypothesis application, `exact`, or other logical moves.

**The one-step proof**: `ext x; exact h x` is even shorter. After
`ext x`, the goal IS `h x`. This works whenever you have a hypothesis
that exactly matches the biconditional you need. This shortcut will
appear frequently in later worlds.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.Subset.antisymm le_antisymm HasSubset.Subset.antisymm subset_antisymm Set.eq_of_subset_of_subset LE.le.antisymm Set.ext_iff
