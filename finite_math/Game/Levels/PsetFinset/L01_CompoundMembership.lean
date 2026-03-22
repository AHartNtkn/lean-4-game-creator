import Game.Metadata

World "PsetFinset"
Level 1

Title "Compound Membership"

Introduction "
# Problem Set: Finsets

Welcome to the finset problem set.

**Your task**: Prove that $5$ belongs to the intersection of two sets:
the odd numbers in `range 8`, and the literal set $\\{3, 5, 7\\}$.

Think about which `mem_*` lemmas unwrap each layer of the goal.
"

/-- 5 is in the odd numbers of range 8 intersected with {3, 5, 7}. -/
Statement : (5 : ℕ) ∈ (Finset.range 8).filter (fun n => n % 2 = 1) ∩ ({3, 5, 7} : Finset ℕ) := by
  Hint (hidden := true) "Use `rw [Finset.mem_inter]` to split the intersection
  membership into two parts, then `constructor`."
  rw [Finset.mem_inter]
  constructor
  -- 5 ∈ (range 8).filter (odd)
  · Hint (hidden := true) "Use `rw [Finset.mem_filter]` then `constructor`.
    First part: `rw [Finset.mem_range]; omega`.
    Second part: `rfl`."
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      omega
    · rfl
  -- 5 ∈ {3, 5, 7}
  · Hint (hidden := true) "Peel inserts with `rw [Finset.mem_insert]` and
    `left`/`right` until you reach `5 = 5`, then `rfl`."
    rw [Finset.mem_insert]
    right
    rw [Finset.mem_insert]
    left
    rfl

Conclusion "
Two skills combined on a fresh surface:
- `mem_inter` splits intersection membership into a conjunction
- `mem_filter` splits filter membership into container + predicate
- `mem_insert` peels literal finsets one element at a time
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right
