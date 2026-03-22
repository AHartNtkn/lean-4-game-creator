import Game.Metadata

World "FinsetOperations"
Level 24

Title "Dual Distributivity"

Introduction "
# Intersection Distributes Over Union

In the previous level you proved that union distributes over
intersection:
$(s \\cup t) \\cap u = (s \\cap u) \\cup (t \\cap u)$.

Now prove the **dual**: intersection distributes over union:

$$(s \\cap t) \\cup u = (s \\cup u) \\cap (t \\cup u)$$

In the Level 22 conclusion, this was described as 'same proof pattern,
swap the roles of $\\land$ and $\\lor$.' Is that actually true? Let's
find out.

After `ext x; simp only [Finset.mem_union, Finset.mem_inter]`, the
goal becomes:

$$(x \\in s \\land x \\in t) \\lor x \\in u \\;\\longleftrightarrow\\; (x \\in s \\lor x \\in u) \\land (x \\in t \\lor x \\in u)$$

The logical content is $(A \\land B) \\lor C \\iff (A \\lor C) \\land (B \\lor C)$
— disjunction distributes over conjunction.

**Forward**: case-split on the `\\lor`. If `x \\in s \\land x \\in t`, build
both conjuncts using `left`. If `x \\in u`, build both using `right`.

**Backward**: case-split on the first conjunct. If `x \\in s`, then
case-split on the second conjunct. If `x \\in u` (from either), you're
done via `right`.

**Your task**: Prove dual distributivity.
"

/-- Intersection distributes over union. -/
Statement (s t u : Finset ℕ) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) := by
  Hint "Apply the unfold-to-logic recipe: `ext x`, then unfold
  operations with `simp only [Finset.mem_union, Finset.mem_inter]`."
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  Hint "The goal is `(x ∈ s ∧ x ∈ t) ∨ x ∈ u ↔ (x ∈ s ∨ x ∈ u) ∧ (x ∈ t ∨ x ∈ u)`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: (x ∈ s ∧ x ∈ t) ∨ x ∈ u → (x ∈ s ∨ x ∈ u) ∧ (x ∈ t ∨ x ∈ u)
  · Hint "Use `intro h` then `cases h with` to split the disjunction."
    intro h
    Hint (hidden := true) "If `hst : x ∈ s ∧ x ∈ t`, build the conjunction:
    `constructor; left; exact hst.1; left; exact hst.2`.
    If `hu : x ∈ u`, build: `constructor; right; exact hu; right; exact hu`."
    cases h with
    | inl hst =>
      Hint (hidden := true) "You have `hst.1 : x ∈ s` and `hst.2 : x ∈ t`.
      Use `constructor` and choose `left` for both parts."
      constructor
      · left; exact hst.1
      · left; exact hst.2
    | inr hu =>
      Hint (hidden := true) "You have `hu : x ∈ u`. Use `constructor` and
      choose `right` for both parts: `right; exact hu`."
      constructor
      · right; exact hu
      · right; exact hu
  -- Backward: (x ∈ s ∨ x ∈ u) ∧ (x ∈ t ∨ x ∈ u) → (x ∈ s ∧ x ∈ t) ∨ x ∈ u
  · Hint "Use `intro h`. Then `h.1` is `x ∈ s ∨ x ∈ u` and
    `h.2` is `x ∈ t ∨ x ∈ u`. Case-split on `h.1` with `cases h.1 with`."
    intro h
    Hint (hidden := true) "If `x ∈ s` (from `h.1`), case-split on `h.2`:
    if `x ∈ t`, choose `left; exact ⟨hs, ht⟩`;
    if `x ∈ u`, choose `right; exact hu`.
    If `x ∈ u` (from `h.1`), choose `right; exact hu` directly."
    cases h.1 with
    | inl hs =>
      Hint (hidden := true) "Case-split on `h.2` with `cases h.2 with`."
      cases h.2 with
      | inl ht =>
        Hint (hidden := true) "`left; exact ⟨hs, ht⟩`."
        left; exact ⟨hs, ht⟩
      | inr hu =>
        Hint (hidden := true) "`right; exact hu`."
        right; exact hu
    | inr hu =>
      Hint (hidden := true) "`right; exact hu`."
      right; exact hu

Conclusion "
You've proved the **dual distributivity** law:
$(s \\cap t) \\cup u = (s \\cup u) \\cap (t \\cup u)$.

Was it really 'the same proof pattern, swapping $\\land$ and $\\lor$'?
Almost — the forward direction was parallel (case-split, rebuild
with `constructor`), but the backward direction required a
**nested case-split**: splitting on `h.1`, then conditionally
splitting on `h.2`. This asymmetry is the difference between
distributing $\\lor$ over $\\land$ (needs one case-split) and
$\\land$ over $\\lor$ (needs nested case-splits).

Together, Levels 23 and 24 show that union and intersection distribute
over each other in both directions — this is the defining property
of a **distributive lattice**, a structure you'll revisit in the
orders and lattices course.

**A deeper connection**: You proved both distributivity laws from
scratch using `ext` + logic. In fact, either one follows from the
other via De Morgan's law. De Morgan *dualizes* $\\cup$ and $\\cap$,
converting one distributivity law into the other. This means the
two laws are not independent — they're two faces of the same coin.
The proof-from-scratch approach is more instructive (it exercises
the logic directly), but the derivation via De Morgan shows the
structural economy underneath.

**The duality principle**: Look back at the identities you've proved
in this world. They come in pairs:

| Identity | Dual |
|---|---|
| $s \\cup s = s$ | $s \\cap s = s$ |
| $s \\cup t = t \\cup s$ | $s \\cap t = t \\cap s$ |
| $(s \\cup t) \\cup u = s \\cup (t \\cup u)$ | $(s \\cap t) \\cap u = s \\cap (t \\cap u)$ |
| $(s \\cup t) \\cap u = (s \\cap u) \\cup (t \\cap u)$ | $(s \\cap t) \\cup u = (s \\cup u) \\cap (t \\cup u)$ |
| $\\lnot(A \\lor B) = \\lnot A \\land \\lnot B$ | $\\lnot(A \\land B) = \\lnot A \\lor \\lnot B$ |

The pattern: swap $\\cup \\leftrightarrow \\cap$ (equivalently,
$\\lor \\leftrightarrow \\land$, or $\\emptyset \\leftrightarrow \\text{univ}$),
and you get the dual identity. This is not a coincidence — it's a
theorem. In any **Boolean algebra** (and finsets form one), every
identity has a valid dual obtained by this swap. Once you prove
commutativity of $\\cup$, you *know* commutativity of $\\cap$ holds
by the same argument with the roles swapped.

This duality is exactly what the lattice notation `\\sup`/`\\inf`
(Level 16) captures: the abstract lattice axioms are self-dual, so
every theorem about `\\sup` has a mirror theorem about `\\inf`.

Next: the boss, which integrates set difference with the
unfold-to-logic recipe.
"

DisabledTactic trivial «decide» native_decide aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm Finset.union_inter_distrib_right Finset.union_inter_distrib_left Finset.inter_union_distrib_right Finset.inter_union_distrib_left Finset.union_self Finset.inter_self inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left sup_inf_self inf_sup_self Finset.union_inter_cancel_left Finset.inter_union_cancel_left sdiff_sup and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or inf_le_left inf_le_right le_sup_left le_sup_right Finset.union_left_comm Finset.union_right_comm Finset.inter_left_comm Finset.inter_right_comm
