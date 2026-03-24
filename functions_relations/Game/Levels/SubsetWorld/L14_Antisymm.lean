import Game.Metadata

World "SubsetWorld"
Level 14

Title "Double Containment"

Introduction "
# An Alternative Route to Set Equality

In Levels 10–11, you proved set equalities using `ext` — reducing to
a membership biconditional and proving both directions.

There is another route: **double containment** (also called
**antisymmetry**). If `s ⊆ t` AND `t ⊆ s`, then `s = t`.

The theorem `Set.Subset.antisymm` captures this:

$$\\texttt{Set.Subset.antisymm} : s \\subseteq t \\to t \\subseteq s \\to s = t$$

If you already have two subset proofs, you can combine them with
`exact Set.Subset.antisymm h1 h2` to get equality directly — no
`ext` needed.

**Your task**: Given `h1 : s ⊆ t` and `h2 : t ⊆ s`, prove `s = t`.
"

/-- Two sets that contain each other are equal. -/
Statement (α : Type) (s t : Set α) (h1 : s ⊆ t) (h2 : t ⊆ s) :
    s = t := by
  Hint "You have `h1 : s ⊆ t` and `h2 : t ⊆ s`. The theorem
  `Set.Subset.antisymm` says exactly that these two facts imply `s = t`.

  Use `exact Set.Subset.antisymm h1 h2`."
  Branch
    apply Set.Subset.antisymm
    · Hint "The first goal is `s ⊆ t`. You have this as `h1`.
      Use `exact h1`."
      exact h1
    · Hint "The second goal is `t ⊆ s`. You have this as `h2`.
      Use `exact h2`."
      exact h2
  Branch
    apply Set.Subset.antisymm h1
    Hint "The remaining goal is `t ⊆ s`. Use `exact h2`."
    exact h2
  Branch
    ext x
    Hint "You chose `ext` instead of `Set.Subset.antisymm` — that works
    too! After `ext x; constructor`, each direction can be proved
    using `h1` or `h2` as functions."
    constructor
    · intro hx
      exact h1 hx
    · intro hx
      exact h2 hx
  Hint (hidden := true) "`exact Set.Subset.antisymm h1 h2` combines the
  two subset proofs into a set equality proof."
  exact Set.Subset.antisymm h1 h2

Conclusion "
`Set.Subset.antisymm` gives you a one-step path from two ⊆ proofs to
set equality. Compare the two routes:

| Route | When to use |
|---|---|
| `ext x; constructor; ...` | When you need to prove both directions from scratch |
| `Set.Subset.antisymm h1 h2` | When you already have both ⊆ proofs in hand |

In practice, many set equality proofs start with `ext` because you
rarely have the subset proofs pre-packaged. But `antisymm` is
valuable when subset facts are available from other lemmas or
hypotheses.

In ordinary math, this is the well-known principle: \"two sets are
equal iff each is a subset of the other.\" Every proof of set equality
by \"double inclusion\" (showing ⊆ in both directions) is implicitly
using antisymmetry.

A **partial order** is a relation that satisfies three properties:
1. **Reflexive**: $a \\leq a$ for all $a$
2. **Transitive**: $a \\leq b$ and $b \\leq c$ imply $a \\leq c$
3. **Antisymmetric**: $a \\leq b$ and $b \\leq a$ imply $a = b$

You have now proved all three for `⊆` on `Set α`:
- **Reflexive**: `Set.Subset.refl` (Level 3)
- **Transitive**: `Set.Subset.trans` (Level 8)
- **Antisymmetric**: `Set.Subset.antisymm` (this level)

Together, these make `⊆` a **partial order** on sets. The partial
order concept is central to mathematics — you will study it in depth
in the Orders \\& Lattices course.

These two routes — `ext` and `antisymm` — are logically *equivalent*.
You can derive `ext` from `antisymm` and `antisymm` from `ext`. You
will prove this equivalence yourself in Levels 16 and 17.
"

/-- `Set.Subset.antisymm` proves that two sets are equal if each is
a subset of the other.

## Statement
```
Set.Subset.antisymm : s ⊆ t → t ⊆ s → s = t
```

## Syntax
```
exact Set.Subset.antisymm h1 h2    -- from two subset proofs
apply Set.Subset.antisymm           -- leaving two subset goals
```

## When to use it
When you have (or can prove) both `s ⊆ t` and `t ⊆ s` and want to
conclude `s = t`. This is the \"double containment\" proof strategy.

## Example
```
-- h1 : s ⊆ t, h2 : t ⊆ s
exact Set.Subset.antisymm h1 h2
-- closes the goal s = t
```
-/
TheoremDoc Set.Subset.antisymm as "Set.Subset.antisymm" in "Set"

NewTheorem Set.Subset.antisymm

/-- `le_antisymm` proves `a ≤ b → b ≤ a → a = b` for any partial order.
For sets, `≤` is `⊆`, so this is another way to prove set equality
from mutual subsets. `Set.Subset.antisymm` is the set-specific version. -/
TheoremDoc le_antisymm as "le_antisymm" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem le_antisymm HasSubset.Subset.antisymm subset_antisymm Set.eq_of_subset_of_subset LE.le.antisymm Set.mem_setOf_eq Set.mem_setOf
