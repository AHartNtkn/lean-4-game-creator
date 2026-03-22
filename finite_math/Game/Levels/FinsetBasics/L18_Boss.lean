import Game.Metadata

World "FinsetBasics"
Level 18

Title "Boss: Finset Fundamentals"

Introduction "
# Boss: Finset Fundamentals

Time to combine everything. You're given a finset `s` that equals
`{2, 4, 6}`, and you must prove five facts about it:

1. **Membership**: `4 ∈ s` — peel inserts to find 4
2. **Non-membership**: `5 ∉ s` — assume membership, derive contradiction
3. **Range coverage**: `∀ x ∈ s, x ∈ Finset.range 7` — every element of `s` is in `range 7`
4. **Nonempty**: `s.Nonempty` — provide a witness element
5. **Universal idempotency**: `∀ x ∈ s, insert x s = s` — combine intro with apply-then-prove

Most parts start with `rw [hs]` to substitute the known value of `s`.
Part 3 combines multiple skills: substitution, intro, reading membership
backward, and range membership. Part 5 combines universally quantified
intro with the apply-then-prove pattern from Level 14.
"

/-- Five fundamental facts about finsets. -/
Statement (s : Finset ℕ) (hs : s = {2, 4, 6}) :
    (4 ∈ s) ∧ (5 ∉ s) ∧ (∀ x ∈ s, x ∈ Finset.range 7) ∧ s.Nonempty ∧ (∀ x ∈ s, insert x s = s) := by
  Hint "The goal is a five-part conjunction. Use `constructor` to split
  off the first part."
  constructor
  -- Part 1: Membership
  · Hint "Substitute `s`: `rw [hs]`. Then prove membership of `4`
    by peeling inserts."
    rw [hs]
    Hint (hidden := true) "Chain the rewrites:
    `rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]`
    gives a three-way disjunction. Then `right; left; rfl`."
    rw [Finset.mem_insert]
    right
    rw [Finset.mem_insert]
    left
    rfl
  Hint "The remaining goal is still a conjunction. Use `constructor`
  to split off the next part."
  constructor
  -- Part 2: Non-membership
  · Hint "Substitute `s`: `rw [hs]`. Then prove non-membership of `5`."
    rw [hs]
    Hint (hidden := true) "`intro h`, then
    `rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h`,
    then `omega`."
    intro h
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
    omega
  Hint "Another conjunction remains. Use `constructor` again."
  constructor
  -- Part 3: Range coverage (all elements of s are in range 7)
  · Hint "Substitute `s`: `rw [hs]`. Then introduce `x` and its
    membership hypothesis with `intro x hx`."
    rw [hs]
    Hint (hidden := true) "After `intro x hx`, unfold `hx` with
    `rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx`,
    then `rw [Finset.mem_range]; omega`."
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    omega
  Hint "Two parts left. Use `constructor` to split them."
  constructor
  -- Part 4: Nonempty
  · Hint "Substitute `s`: `rw [hs]`. Then prove `Nonempty` by
    providing a witness with `use`."
    rw [hs]
    Hint (hidden := true) "`use 2; rw [Finset.mem_insert]; left; rfl`
    provides 2 as the witness and proves its membership."
    use 2
    rw [Finset.mem_insert]
    left
    rfl
  -- Part 5: Universal insert idempotency
  · Hint "Substitute `s`: `rw [hs]`. Then introduce `x` and its
    membership hypothesis with `intro x hx`."
    rw [hs]
    Hint (hidden := true) "After `intro x hx`, use
    `apply Finset.insert_eq_of_mem` to reduce to a membership proof,
    then `exact hx`."
    intro x hx
    Hint "Now use the apply-then-prove pattern:
    `apply Finset.insert_eq_of_mem` reduces the equation to membership."
    apply Finset.insert_eq_of_mem
    Hint (hidden := true) "The goal is membership of `x` in the
    concrete set — but you already have `{hx}`. Use `exact {hx}`."
    exact hx

Conclusion "
Congratulations — you've completed **Finset Basics**!

Your finset toolkit:

| Move | Tool | Learned in |
|---|---|---|
| Prove `a ∈ insert b s` | `rw [Finset.mem_insert]` then `left`/`right` | Level 1 |
| Prove `a ∈ {{b}}` (singleton) | `rw [Finset.mem_singleton]` | Level 2 |
| Prove `a ∉ ∅` | `exact Finset.notMem_empty a` | Level 3 |
| Prove `m ∈ Finset.range n` | `rw [Finset.mem_range]; omega` | Level 4-8 |
| Prove `m ∉ Finset.range n` | `intro h; rw [Finset.mem_range] at h; omega` | Level 5, 11 |
| Prove range 0 is empty | non-membership for all elements | Level 6 |
| Bridge `Fin n` to `Finset.range n` | `rw [Finset.mem_range]; exact i.isLt` | Level 9-10 |
| Prove `a ∉ {{b, c, d}}` | `intro h; rw [mem_insert, ...] at h; omega` | Level 12 |
| Unfold `h : x ∈ {{a, b, c}}` | `rw [mem_insert, ...] at h` | Level 13 |
| Prove `insert a s = s` | `apply Finset.insert_eq_of_mem` (apply-then-prove) | Level 14 |
| Extract from `s.Nonempty` | `obtain ⟨x, hx⟩ := hs` | Level 15 |
| Prove `s.Nonempty` | `use a` then prove `a ∈ s` | Level 16 |
| Close concrete goals | `decide` | Level 17 |

**One thing this world can't do yet**: prove that two finsets are
**equal**. You showed membership and non-membership, but proving
`{{1, 2, 3}} = {{3, 1, 2}}` (same elements, different order) requires
showing every element of one is in the other. That's the job of the
`ext` tactic, which you'll learn in the FinsetOperations world.

**Also missing**: you can prove *what's in* a finset, but not
*how many* elements it has. The number of elements is `s.card`
(the **cardinality**), and you'll learn to compute it in the
Cardinality world.

**What's next**: You now know how to build finsets and test
membership. Next: what happens when you *combine* finsets? Union
(`∪`), intersection (`∩`), and set difference (`\\`) give finsets
an algebraic structure, and the `ext` tactic lets you prove two
finsets are equal by showing they have the same members.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.insert_nonempty Finset.singleton_nonempty Finset.not_mem_range_self
