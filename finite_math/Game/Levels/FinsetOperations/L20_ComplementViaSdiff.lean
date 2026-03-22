import Game.Metadata

World "FinsetOperations"
Level 20

Title "Complement via Set Difference"

Introduction "
# Double Set Difference and Complement

Here's a useful identity that connects set difference to intersection:

$$s \\setminus (s \\setminus t) = s \\cap t$$

Read it aloud: 'removing from `s` everything that's in `s` but not in `t`
leaves exactly the elements of `s` that *are* in `t`.'

This is the **complement principle**: if you think of `s` as a 'universe,'
then `s \\\\ t` is the 'complement of `t` within `s`.' Taking the complement
again (`s \\\\ (s \\\\ t)`) gets you back to `s ∩ t` — the part of `t` inside
your universe.

After `ext x` and rewriting with `Finset.mem_sdiff` (twice) and
`Finset.mem_inter`, the goal becomes:

$$x \\in s \\land \\neg(x \\in s \\land x \\notin t) \\;\\longleftrightarrow\\; x \\in s \\land x \\in t$$

The backward direction is straightforward: if `x ∈ s ∧ x ∈ t`, then
`x ∈ s` is immediate, and `¬(x ∈ s ∧ x ∉ t)` follows because `x ∈ t`
contradicts `x ∉ t`.

The forward direction needs `by_contra`: you need `x ∈ t`, but your
hypotheses only tell you `x ∈ s` and `¬(x ∈ s ∧ x ∉ t)`. Assume
`x ∉ t` (using `by_contra`), then construct `⟨h.1, hnt⟩ : x ∈ s ∧ x ∉ t`,
which contradicts `h.2`.

Note: `simp` is disabled for this level to ensure you practice the
`by_contra` technique manually.

**Your task**: Prove that $s \\setminus (s \\setminus t) = s \\cap t$.
"

/-- Double set difference recovers intersection: s \ (s \ t) = s ∩ t. -/
Statement (s t : Finset ℕ) : s \ (s \ t) = s ∩ t := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Use `rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_inter]`
  to unfold all operations into logic."
  rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_inter]
  Hint "The goal is
  `x ∈ s ∧ ¬(x ∈ s ∧ x ∉ t) ↔ x ∈ s ∧ x ∈ t`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: x ∈ s ∧ ¬(x ∈ s ∧ x ∉ t) → x ∈ s ∧ x ∈ t
  · Hint "Use `intro h`. Then `h.1 : x ∈ s` and
    `h.2 : ¬(x ∈ s ∧ x ∉ t)`. The first conjunct of the goal
    is `h.1`. For the second (`x ∈ t`), use `by_contra`."
    intro h
    Hint (hidden := true) "Use `constructor` to split the goal.
    First part: `exact h.1`. Second part: `by_contra hnt`
    introduces `hnt : x ∉ t`, then `exact h.2 ⟨h.1, hnt⟩`."
    constructor
    · exact h.1
    · Hint "The goal is `x ∈ t`. You can't extract this directly
      from `h`. Use `by_contra hnt` to assume `x ∉ t` and derive
      a contradiction."
      by_contra hnt
      Hint (hidden := true) "Now `hnt : x ∉ t`. Build the
      contradicting pair: `exact h.2 ⟨h.1, hnt⟩`."
      exact h.2 ⟨h.1, hnt⟩
  -- Backward: x ∈ s ∧ x ∈ t → x ∈ s ∧ ¬(x ∈ s ∧ x ∉ t)
  · Hint "Use `intro h`. Then `h.1 : x ∈ s` and `h.2 : x ∈ t`.
    Use `constructor` to split the goal."
    intro h
    Hint (hidden := true) "First part: `exact h.1`. Second part:
    `intro hc; exact hc.2 h.2` — assume `hc : x ∈ s ∧ x ∉ t`,
    then `hc.2 : x ∉ t` contradicts `h.2 : x ∈ t`."
    constructor
    · exact h.1
    · intro hc
      exact hc.2 h.2

Conclusion "
You've proved the **double set difference identity**:
$s \\setminus (s \\setminus t) = s \\cap t$.

The key move was `by_contra`: assume `¬(goal)` and derive `False`.
Combined with the negated conjunction hypothesis, this extracted
positive membership information from a double negation.

**The complement perspective**: Think of `s` as a 'universe.' Then:
- `s \\\\ t` is the 'complement of `t` within `s`' — everything in
  the universe that isn't in `t`
- `s \\\\ (s \\\\ t)` is the 'complement of the complement' — which
  gives back `s ∩ t`

This double-complement pattern is exactly the set-theoretic version
of double negation: $\\neg\\neg P \\iff P$. It previews the
**inclusion-exclusion** reasoning you'll use in the Cardinality world,
where counting elements 'not in the complement' is a key technique.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self sdiff_sup Finset.sdiff_inter_distrib_left and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or sdiff_sdiff_right_self inf_le_left inf_le_right le_sup_left le_sup_right Finset.sdiff_sdiff_self_left
