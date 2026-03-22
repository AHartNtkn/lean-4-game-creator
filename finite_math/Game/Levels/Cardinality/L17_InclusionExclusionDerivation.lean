import Game.Metadata

World "Cardinality"
Level 17

Title "Why Inclusion-Exclusion Works"

Introduction "
# Deriving Inclusion-Exclusion

In Level 13, you used `card_union_add_card_inter` as a library
theorem: you cited it, applied it, and moved on. Now you have all
the tools to understand *why* it's true.

The derivation uses two facts you've already proved:

**From Level 15** (disjoint union):
$$\\text{Disjoint}\\; s\\; t \\;\\Rightarrow\\; |s \\cup t| = |s| + |t|$$

**From Level 16** (complement counting):
$$|s \\setminus t| + |s \\cap t| = |s|$$

The key observation: $s \\setminus t$ and $t$ are **always disjoint**
(an element can't both be 'in $s$ but not in $t$' and 'in $t$'),
and their union is $s \\cup t$. Therefore:

$$|s \\cup t| = |s \\setminus t| + |t|$$

Combining with complement counting ($|s \\setminus t| = |s| - |s \\cap t|$):
$$|s \\cup t| = |s| - |s \\cap t| + |t|$$

which rearranges to inclusion-exclusion:
$$|s \\cup t| + |s \\cap t| = |s| + |t|$$

**Your task**: Derive inclusion-exclusion using `card_union_of_disjoint`,
`sdiff_disjoint`, `sdiff_sup_self`, and `card_sdiff_add_card_inter`.
The derivation is three `have` lines followed by `omega`.
"

/-- Derive inclusion-exclusion from disjoint union and complement counting. -/
Statement (s t : Finset ℕ) :
    (s ∪ t).card + (s ∩ t).card = s.card + t.card := by
  Hint "Step 1: The disjoint union `(s \\ t) ∪ t` has cardinality
  `(s \\ t).card + t.card`. Use:
  `have h1 := Finset.card_union_of_disjoint (disjoint_sdiff_self_left : Disjoint (s \\ t) t)`"
  Hint (hidden := true) "Try:
  `have h1 := Finset.card_union_of_disjoint (disjoint_sdiff_self_left : Disjoint (s \\ t) t)`"
  have h1 := Finset.card_union_of_disjoint (disjoint_sdiff_self_left : Disjoint (s \ t) t)
  Hint "Step 2: The union `(s \\ t) ∪ t` equals `s ∪ t`.
  Rewrite `h1` to be about `s ∪ t` instead of `(s \\ t) ∪ t`.
  Use `sdiff_sup_self` which says `s \\ t ⊔ t = s ⊔ t` (where ⊔ is ∪ for finsets)."
  Hint (hidden := true) "Try:
  `have h2 : s \\ t ∪ t = s ∪ t := sdiff_sup_self t s`
  `rw [h2] at h1`"
  have h2 : s \ t ∪ t = s ∪ t := sdiff_sup_self t s
  rw [h2] at h1
  Hint "Step 3: Complement counting gives `(s \\ t).card + (s ∩ t).card = s.card`.
  Use `Finset.card_sdiff_add_card_inter` from Level 16."
  Hint (hidden := true) "Try:
  `have h3 := Finset.card_sdiff_add_card_inter s t`
  then `omega`."
  have h3 := Finset.card_sdiff_add_card_inter s t
  Hint "Now `omega` sees:
  - `h1 : (s ∪ t).card = (s \\ t).card + t.card`
  - `h3 : (s \\ t).card + (s ∩ t).card = s.card`
  - Goal: `(s ∪ t).card + (s ∩ t).card = s.card + t.card`

  This is linear arithmetic: from h1 and h3, eliminate `(s \\ t).card`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
You **derived** inclusion-exclusion from two simpler principles:

1. **Disjoint union**: $|A \\cup B| = |A| + |B|$ when $A \\cap B = \\emptyset$
2. **Complement counting**: $|s \\setminus t| + |s \\cap t| = |s|$

The derivation chain:
- $s \\setminus t$ and $t$ are disjoint ($\\to$ `card_union_of_disjoint`)
- $(s \\setminus t) \\cup t = s \\cup t$ ($\\to$ `sdiff_sup_self`)
- So $|s \\cup t| = |s \\setminus t| + |t|$
- And $|s \\setminus t| = |s| - |s \\cap t|$ ($\\to$ `card_sdiff_add_card_inter`)
- Therefore $|s \\cup t| + |s \\cap t| = |s| + |t|$

In Level 13, you used `card_union_add_card_inter` as a black box.
Now you know that inclusion-exclusion is not an independent axiom —
it's a consequence of the partition identity from FinsetOperations.
Every counting identity in this world traces back to set
decompositions.

**New tool**: `sdiff_sup_self` says $s \\setminus t \\cup t = s \\cup t$.
This is a lattice identity: removing elements not in $t$ from $s$,
then adding back all of $t$, gives the same result as just taking
$s \\cup t$.
"

/-- `sdiff_sup_self` states that `a \\ b ⊔ b = a ⊔ b`.

For finsets: `s \\ t ∪ t = s ∪ t`.

## Syntax
```
have h : s \\ t ∪ t = s ∪ t := sdiff_sup_self
```

## When to use it
When you need to relate `s \\ t ∪ t` to `s ∪ t`. This identity
says: removing elements of `t` from `s`, then adding `t` back,
gives the same as just taking the union.
-/
TheoremDoc sdiff_sup_self as "sdiff_sup_self" in "Finset"

/-- `disjoint_sdiff_self_left` states that `Disjoint (a \\ b) b`.

For finsets: `s \\ t` and `t` share no elements.

## Syntax
```
have h : Disjoint (s \\ t) t := disjoint_sdiff_self_left
```

## When to use it
When you need to apply `card_union_of_disjoint` to `s \\ t` and `t`.
The disjointness is automatic: an element in `s \\ t` is by definition
not in `t`.
-/
TheoremDoc disjoint_sdiff_self_left as "disjoint_sdiff_self_left" in "Finset"

NewTheorem sdiff_sup_self disjoint_sdiff_self_left

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.card_union_add_card_inter
