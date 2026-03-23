import Game.Metadata

World "Finale"
Level 9

Title "Three-Part Decomposition"

Introduction "
# Double Counting via Set Decomposition

Any union $A \\cup B$ decomposes into three disjoint parts:

- $A \\setminus B$ — elements in $A$ only
- $B \\setminus A$ — elements in $B$ only
- $A \\cap B$ — elements in both

Counting each part and summing should give $|A \\cup B|$.
Prove this identity by combining three cardinality lemmas
from the Cardinality world.

**The tools you need**:
- `Finset.card_sdiff_add_card_inter s t` :
  $|s \\setminus t| + |s \\cap t| = |s|$
- `Finset.card_union_add_card_inter s t` :
  $|s \\cup t| + |s \\cap t| = |s| + |t|$
- `Finset.inter_comm s t` : $s \\cap t = t \\cap s$

Apply these with both argument orders and combine with `omega`.
"

/-- The three-part decomposition of a union. -/
Statement (s t : Finset ℕ) :
    (s \ t).card + (t \ s).card + (s ∩ t).card = (s ∪ t).card := by
  Hint "Gather the cardinality identities you need. Start with
  `card_sdiff_add_card_inter` applied to both `s t` and `t s`."
  Hint (hidden := true) "Try:
  `have h1 := Finset.card_sdiff_add_card_inter s t`
  `have h2 := Finset.card_sdiff_add_card_inter t s`"
  have h1 := Finset.card_sdiff_add_card_inter s t
  have h2 := Finset.card_sdiff_add_card_inter t s
  Hint "`h2` uses `t ∩ s` but the goal uses `s ∩ t`. Rewrite
  `h2` using `Finset.inter_comm` to align the intersection."
  Hint (hidden := true) "Try:
  `rw [Finset.inter_comm t s] at h2`"
  rw [Finset.inter_comm t s] at h2
  Hint "Now get the union-intersection identity."
  Hint (hidden := true) "Try:
  `have h3 := Finset.card_union_add_card_inter s t`"
  have h3 := Finset.card_union_add_card_inter s t
  Hint "All the pieces are in place. `omega` can close the
  goal from the three arithmetic identities."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
**Double counting by decomposition**: you counted the union
$A \\cup B$ by splitting it into three disjoint parts and
summing their sizes.

The tools came from Phases 2 and 3:
- `card_sdiff_add_card_inter` twice (for $s,t$ and $t,s$)
- `inter_comm` to align $t \\cap s$ with $s \\cap t$
- `card_union_add_card_inter` once
- `omega` to close the arithmetic

**Connection to Phases 2 and 3**: This level integrates
Finset operations ($\\cup$, $\\cap$, $\\setminus$) from Phase 2
with the cardinality identities from Phase 3. The
decomposition pattern — split a set into disjoint parts,
count each part, sum — is the same strategy behind fiber
decomposition and inclusion-exclusion.

**The double-counting principle**: whenever you can count the
same set two different ways, the counts must agree. Here the
'two ways' are: directly ($|A \\cup B|$) and by decomposition
($|A \\setminus B| + |B \\setminus A| + |A \\cap B|$). The
identity holds because the decomposition is a partition.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
-- Lattice aliases for Finset operations
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_le inf_sup_right inf_sup_left sup_inf_right sup_inf_left sup_eq_left inf_eq_left
