import Game.Metadata

World "FinsetOperations"
Level 25

Title "Boss: De Morgan's Second Law"

Introduction "
# Boss: Set Difference Distributes Over Intersection

Time to combine everything from this world. You'll prove a set identity
that integrates the unfold-to-logic recipe with set difference and
proof by contradiction:

$$s \\setminus (t \\cap u) = (s \\setminus t) \\cup (s \\setminus u)$$

This is **De Morgan's second law** for sets: removing elements in
*both* `t` and `u` is the same as taking elements removed from `t`
OR removed from `u`.

Compare with Level 17 (De Morgan's first law):
$s \\setminus (t \\cup u) = (s \\setminus t) \\cap (s \\setminus u)$.
The first law swaps union to intersection; this one swaps intersection
to union.

After `ext x; simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]`,
the goal becomes:

$$x \\in s \\land \\neg(x \\in t \\land x \\in u) \\;\\longleftrightarrow\\; (x \\in s \\land x \\notin t) \\lor (x \\in s \\land x \\notin u)$$

The **backward direction** is straightforward: from either side of the
disjunction, extract `x \\in s` and derive the negated conjunction by
applying the non-membership to a component.

The **forward direction** is the challenge. You have `x \\in s` and
`\\neg(x \\in t \\land x \\in u)`, but you need to produce `x \\notin t`
or `x \\notin u` — positive non-membership information from a negated
conjunction. This requires **nested** `by_contra` — a `by_contra`
inside a `by_contra`. The outer `by_contra` assumes the disjunction
is false; the inner ones prove each component by contradiction.
This nesting pattern is new — here's the strategy:

1. Assume the goal is false (neither disjunct holds)
2. Show that this forces both `x \\in t` and `x \\in u`
3. Contradiction with `\\neg(x \\in t \\land x \\in u)`

The skill integration:
- **ext** (Level 8): convert set equality to logic
- **mem_sdiff, mem_inter, mem_union** (Levels 1-3): convert to logic
- **simp only** (Level 16): unfold all at once
- **by_contra** (Level 18): assume the negation and derive contradiction
- **have** (from NNG4): build intermediate results
- **constructor, cases, .1, .2, left, right**: standard logic handling
"

/-- De Morgan's second law for sets. -/
Statement (s t u : Finset ℕ) : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := by
  Hint "Apply the unfold-to-logic recipe: `ext x`, then
  `simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]`."
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
  Hint "The goal is
  `x ∈ s ∧ ¬(x ∈ t ∧ x ∈ u) ↔ (x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∉ u)`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: x ∈ s ∧ ¬(x ∈ t ∧ x ∈ u) → (x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∉ u)
  · Hint "Use `intro h`. Then `h.1 : x ∈ s` and
    `h.2 : ¬(x ∈ t ∧ x ∈ u)`. You need to produce
    `(x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∉ u)`.

    The challenge: you know `x ∈ t` and `x ∈ u` can't BOTH hold,
    but you don't know which one fails. Use `by_contra` to assume
    the whole goal is false, then show both must hold — contradiction."
    intro h
    Hint (hidden := true) "Use `by_contra h_neg`. This gives
    `h_neg : ¬((x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∉ u))` and changes
    the goal to `False`.

    Strategy: show `x ∈ t` (if not, the left disjunct holds,
    contradicting h_neg). Similarly show `x ∈ u`. Then
    `h.2 (And.intro ht hu)` gives `False`."
    by_contra h_neg
    Hint "The goal is `False`. You need to show that `h.2` and `h_neg`
    are contradictory.

    Use `apply h.2` to change the goal to `x ∈ t ∧ x ∈ u` — if you
    can build that, `h.2` derives `False`."
    apply h.2
    Hint "The goal is `x ∈ t ∧ x ∈ u`. Use `constructor` to split it."
    constructor
    -- Prove x ∈ t
    · Hint "The goal is `x ∈ t`. Use `by_contra hnt` to assume `x ∉ t`
      and derive a contradiction with `h_neg`."
      by_contra hnt
      Hint (hidden := true) "You have `hnt : x ∉ t`. Then
      `⟨h.1, hnt⟩ : x ∈ s ∧ x ∉ t`, so
      `Or.inl ⟨h.1, hnt⟩ : (x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∉ u)`.
      This contradicts `h_neg`.
      Use `apply h_neg; left; exact ⟨h.1, hnt⟩`."
      apply h_neg
      left
      exact ⟨h.1, hnt⟩
    -- Prove x ∈ u
    · Hint "Same pattern: `by_contra hnu` then derive a contradiction."
      by_contra hnu
      Hint (hidden := true) "`apply h_neg; right; exact ⟨h.1, hnu⟩`."
      apply h_neg
      right
      exact ⟨h.1, hnu⟩
  -- Backward: (x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∉ u) → x ∈ s ∧ ¬(x ∈ t ∧ x ∈ u)
  · Hint "Use `intro h` then `cases h with` to split the disjunction."
    intro h
    Hint (hidden := true) "In each case, build the conjunction:
    `h.1` gives `x ∈ s`, and for `¬(x ∈ t ∧ x ∈ u)`, use
    `intro htu` and apply the non-membership to a component of `htu`."
    cases h with
    | inl hst =>
      Hint (hidden := true) "You have `hst.1 : x ∈ s` and `hst.2 : x ∉ t`.
      Use `constructor`. First part: `exact hst.1`.
      Second part: `intro htu; exact hst.2 htu.1`."
      constructor
      · exact hst.1
      · intro htu
        exact hst.2 htu.1
    | inr hsu =>
      Hint (hidden := true) "You have `hsu.1 : x ∈ s` and `hsu.2 : x ∉ u`.
      Use `constructor`. First part: `exact hsu.1`.
      Second part: `intro htu; exact hsu.2 htu.2`."
      constructor
      · exact hsu.1
      · intro htu
        exact hsu.2 htu.2

Conclusion "
Congratulations — you've completed **Finset Operations**!

You proved De Morgan's second law for sets:
$s \\setminus (t \\cap u) = (s \\setminus t) \\cup (s \\setminus u)$.

The forward direction required the most sophisticated use of
`by_contra` yet: you assumed the *entire disjunction* was false,
then showed this forces both `x \\in t` and `x \\in u`, contradicting
the negated conjunction. Each component (`x \\in t`, `x \\in u`) was
itself proven by contradiction — a nested use of `by_contra`.

Together with Level 17 (De Morgan's first law), you've proven both
De Morgan laws for sets:
- $s \\setminus (t \\cup u) = (s \\setminus t) \\cap (s \\setminus u)$
- $s \\setminus (t \\cap u) = (s \\setminus t) \\cup (s \\setminus u)$

These mirror the propositional De Morgan laws:
- $\\neg(P \\lor Q) \\iff \\neg P \\land \\neg Q$
- $\\neg(P \\land Q) \\iff \\neg P \\lor \\neg Q$

Your finset operations toolkit:

| Operation | Membership lemma | Logic form |
|---|---|---|
| `s ∪ t` | `Finset.mem_union` | `a ∈ s ∨ a ∈ t` |
| `s ∩ t` | `Finset.mem_inter` | `a ∈ s ∧ a ∈ t` |
| `s \\\\ t` | `Finset.mem_sdiff` | `a ∈ s ∧ a ∉ t` |
| `s.filter p` | `Finset.mem_filter` | `a ∈ s ∧ p a` |
| `s ⊆ t` | `Finset.subset_iff` | `∀ x ∈ s, x ∈ t` |
| `s = t` | `ext` / `Finset.ext_iff` | `∀ x, x ∈ s ↔ x ∈ t` |

The proof recipe for any set identity:
1. `ext x` — reduce to element-wise logic
2. `simp only [mem_union, mem_inter, ...]` — unfold all operations
3. Handle the resulting ∧/∨/¬ with `constructor`, `cases`, `left`/`right`
4. When stuck on extracting positive from negative: `by_contra`

**The bigger picture**: Across this world, you've proved the key
axioms of a **distributive lattice with difference**:

| Property | Level | Statement |
|---|---|---|
| Idempotency | L09, L12 | $s \\cap s = s$, $s \\cup s = s$ |
| Commutativity | L13, L14 | $s \\cap t = t \\cap s$, $s \\cup t = t \\cup s$ |
| Associativity | L15 | $(s \\cup t) \\cup u = s \\cup (t \\cup u)$ |
| Identity | L10 | $s \\cup \\emptyset = s$ |
| Absorption | L22 | $s \\cup (s \\cap t) = s$ |
| Distributivity | L23, L24 | both directions |
| De Morgan | L18, L25 | both laws |

To get a full **Boolean algebra**, you'd also need a complement
operation ($s^c$) and complement laws ($s \\cap s^c = \\emptyset$,
$s \\cup s^c = U$). Finsets don't have a natural complement —
that requires a universal set `U`, which you'll meet in the
Cardinality world as `Finset.univ`. For now, set difference
(`\\setminus`) plays the role of a relative complement.

**What's next**: The next world covers `Finset.image` — applying a
function to every element of a finset, and the relationship between
injectivity and cardinality of images.
"

DisabledTactic trivial «decide» native_decide aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm Finset.union_inter_distrib_right Finset.union_inter_distrib_left Finset.inter_union_distrib_right Finset.inter_union_distrib_left Finset.union_self Finset.inter_self inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left sup_inf_self inf_sup_self Finset.union_inter_cancel_left Finset.inter_union_cancel_left sdiff_sup sdiff_inf Finset.sdiff_union_distrib Finset.sdiff_inter_distrib_left Finset.sdiff_sdiff_self_left sdiff_sdiff_right_self and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or not_and_or inf_le_left inf_le_right le_sup_left le_sup_right Finset.union_left_comm Finset.union_right_comm Finset.inter_left_comm Finset.inter_right_comm
