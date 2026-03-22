import Game.Metadata

World "FinsetOperations"
Level 18

Title "De Morgan's Law"

Introduction "
# De Morgan's Law for Finsets

Remember set difference from Level 3? `s \\\\ t` contains elements in `s`
but not in `t`, with `mem_sdiff : x ∈ s \\\\ t ↔ x ∈ s ∧ x ∉ t`.

Now you'll prove a fundamental identity connecting set difference with
union and intersection — **De Morgan's law for sets**:

$$s \\setminus (t \\cup u) = (s \\setminus t) \\cap (s \\setminus u)$$

In words: removing elements that are in `t` *or* `u` is the same as
removing elements in `t` AND removing elements in `u`, then taking
the intersection.

After `ext x` and `simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]`,
the goal becomes pure logic:

$$x \\in s \\land \\neg(x \\in t \\lor x \\in u) \\;\\longleftrightarrow\\; (x \\in s \\land x \\notin t) \\land (x \\in s \\land x \\notin u)$$

This is the propositional De Morgan's law: $\\neg(P \\lor Q) \\iff \\neg P \\land \\neg Q$,
wrapped in the common `x ∈ s` hypothesis.

**New move**: To prove a negation like `x ∉ t` (which is `x ∈ t → False`),
use `intro ht` to assume membership, then derive a contradiction using
`apply h.2` (where `h.2 : ¬(x ∈ t ∨ x ∈ u)`) and `left` or `right`.

**Nested projections**: In the backward direction, you'll encounter a
nested conjunction `h : (x ∈ s ∧ x ∉ t) ∧ (x ∈ s ∧ x ∉ u)`. You can
chain `.1`/`.2` projections to reach any component:
- `h.1.1 : x ∈ s` (first component of the first conjunct)
- `h.1.2 : x ∉ t` (second component of the first conjunct)
- `h.2.1 : x ∈ s` (first component of the second conjunct)
- `h.2.2 : x ∉ u` (second component of the second conjunct)

This extends the `.1`/`.2` pattern from Level 12 to nested conjunctions.

**Your task**: Prove De Morgan's law for finsets.
"

/-- De Morgan's law: s \ (t ∪ u) = (s \ t) ∩ (s \ u). -/
Statement (s t u : Finset ℕ) : s \ (t ∪ u) = (s \ t) ∩ (s \ u) := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Use `simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]`
  to unfold all operations into pure logic."
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  Hint "The goal is now:
  `x ∈ s ∧ ¬(x ∈ t ∨ x ∈ u) ↔ (x ∈ s ∧ x ∉ t) ∧ (x ∈ s ∧ x ∉ u)`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: x ∈ s ∧ ¬(x ∈ t ∨ x ∈ u) → (x ∈ s ∧ x ∉ t) ∧ (x ∈ s ∧ x ∉ u)
  · Hint "Use `intro h`. Then `h.1 : x ∈ s` and `h.2 : ¬(x ∈ t ∨ x ∈ u)`.
    The goal is a conjunction of conjunctions — use `constructor` to split."
    intro h
    Hint (hidden := true) "After `constructor`, each subgoal is a conjunction.
    Use `constructor` again. For the `x ∈ s` parts, use `exact h.1`.
    For the `x ∉ t` part: `intro ht; apply h.2; left; exact ht`.
    For the `x ∉ u` part: `intro hu; apply h.2; right; exact hu`."
    constructor
    · constructor
      · exact h.1
      · Hint (hidden := true) "The goal is `x ∉ t`, which means `x ∈ t → False`.
        Use `intro ht` to assume `x ∈ t`. Then `apply h.2` changes the
        goal to `x ∈ t ∨ x ∈ u`. Choose `left; exact ht`."
        intro ht
        apply h.2
        left
        exact ht
    · constructor
      · exact h.1
      · intro hu
        apply h.2
        right
        exact hu
  -- Backward: (x ∈ s ∧ x ∉ t) ∧ (x ∈ s ∧ x ∉ u) → x ∈ s ∧ ¬(x ∈ t ∨ x ∈ u)
  · Hint "Use `intro h`. Now `h` is a nested conjunction:
    `h.1.1 : x ∈ s`, `h.1.2 : x ∉ t`, `h.2.2 : x ∉ u`.
    Build the goal with `constructor`."
    intro h
    Hint "Use `constructor` to split the goal. The first part
    is `x ∈ s` — use `exact h.1.1`. The second part is
    `¬(x ∈ t ∨ x ∈ u)` — you'll handle that next."
    constructor
    · exact h.1.1
    · Hint "The goal is `¬(x ∈ t ∨ x ∈ u)`, which means
      `(x ∈ t ∨ x ∈ u) → False`. Use `intro hor` to assume
      the disjunction, then `cases hor with` to split into cases."
      intro hor
      Hint (hidden := true) "In each case, derive `False`:
      - `| inl ht =>`: use `exact h.1.2 ht` (since `h.1.2 : x ∉ t`)
      - `| inr hu =>`: use `exact h.2.2 hu` (since `h.2.2 : x ∉ u`)"
      cases hor with
      | inl ht => exact h.1.2 ht
      | inr hu => exact h.2.2 hu

Conclusion "
You've proved De Morgan's law for finsets! The set-level identity

$$s \\setminus (t \\cup u) = (s \\setminus t) \\cap (s \\setminus u)$$

is exactly the propositional De Morgan's law
$\\neg(P \\lor Q) \\iff \\neg P \\land \\neg Q$
lifted to set membership.

The new technique: **proving a negation by applying a negation hypothesis**.
When the goal is `False` and you have `h.2 : ¬(P ∨ Q)`, using `apply h.2`
changes the goal to `P ∨ Q`, which you can then build with `left`/`right`.

This completes the set-operations-are-logic correspondence:
- Union `∪` ↔ disjunction `∨`
- Intersection `∩` ↔ conjunction `∧`
- Set difference `\\\\` ↔ conjunction with negation `∧ ¬`
- De Morgan connects them all.

**Duality**: There is a second De Morgan law:
$s \\setminus (t \\cap u) = (s \\setminus t) \\cup (s \\setminus u)$
(swap ∪ and ∩ everywhere). The two laws are **duals** of each other —
this is a systematic phenomenon from Boolean algebra, not a coincidence.
Every identity involving ∪ and ∩ has a dual obtained by swapping them.
You will prove the second law in the Boss.
"

DisabledTactic trivial «decide» native_decide aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self sdiff_sup Finset.sdiff_inter_distrib_left and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or inf_le_left inf_le_right le_sup_left le_sup_right Finset.sdiff_union_distrib
