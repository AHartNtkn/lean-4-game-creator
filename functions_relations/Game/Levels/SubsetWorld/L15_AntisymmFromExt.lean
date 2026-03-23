import Game.Metadata

World "SubsetWorld"
Level 15

Title "Deriving Antisymmetry from Extensionality"

Introduction "
# Proving Antisymmetry Without `Set.Subset.antisymm`

In Level 13, you used `Set.Subset.antisymm` to combine two subset
proofs into an equality. But you can also derive the same result
using only `ext` — proving that the two approaches are interchangeable.

Given `h1 : s ⊆ t` and `h2 : t ⊆ s`, prove `s = t` using `ext`
and the subset hypotheses as functions. `Set.Subset.antisymm` is
disabled for this level.

**Proof plan**:
1. `ext x` — reduce to a membership `↔`
2. `constructor` — split the `↔`
3. **Forward**: `intro hx; exact h1 hx` — use `h1` as a function
4. **Backward**: `intro hx; exact h2 hx` — use `h2` as a function
"

/-- Deriving set equality from mutual subsets using `ext`. -/
Statement (α : Type) (s t : Set α) (h1 : s ⊆ t) (h2 : t ⊆ s) :
    s = t := by
  Hint "Without `Set.Subset.antisymm`, use `ext x` to reduce
  the equality to membership equivalences."
  ext x
  Hint "Now `constructor` to split the `↔` into two directions."
  constructor
  -- Forward: x ∈ s → x ∈ t
  · Hint "The forward direction: assume `x ∈ s` and show `x ∈ t`.
    The hypothesis `h1 : s ⊆ t` is a function from `x ∈ s` to `x ∈ t`.
    Use `intro hx` then `exact h1 hx`."
    intro hx
    Hint "`h1` applied to `hx` gives `x ∈ t`. Use `exact h1 hx`."
    exact h1 hx
  -- Backward: x ∈ t → x ∈ s
  · Hint "The backward direction: assume `x ∈ t` and show `x ∈ s`.
    Use `h2` the same way: `intro hx` then `exact h2 hx`."
    intro hx
    Hint "`h2` applied to `hx` gives `x ∈ s`. Use `exact h2 hx`."
    exact h2 hx

Conclusion "
You just proved antisymmetry from extensionality! Compare the two proofs:

**Using `Set.Subset.antisymm`** (Level 13):
```
exact Set.Subset.antisymm h1 h2
```

**Using `ext`** (this level):
```
ext x; constructor
· intro hx; exact h1 hx
· intro hx; exact h2 hx
```

The `ext` proof is longer but reveals what is happening: subset
hypotheses `h1` and `h2` serve as the forward and backward directions
of the membership biconditional. This is why `⊆` in both directions
implies `=` — it is precisely the data needed for `↔` on every element.

You have now shown one direction of the equivalence: that `ext` can
simulate `antisymm`. In the next level, you will prove the other
direction — deriving extensionality from antisymmetry — completing the
proof that the two approaches are interchangeable.

Choose based on *convenience*: `antisymm` when you have subset proofs
in hand, `ext` when you want to work element-by-element.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.Subset.antisymm le_antisymm HasSubset.Subset.antisymm subset_antisymm Set.eq_of_subset_of_subset LE.le.antisymm Set.mem_setOf_eq Set.mem_setOf
