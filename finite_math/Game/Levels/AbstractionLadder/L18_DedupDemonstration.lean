import Game.Metadata

World "AbstractionLadder"
Level 18

Title "Dedup in Action"

Introduction "
# What toFinset Does with Duplicates

You just proved that nodup lists have `toFinset.card = length` — no
elements are lost. But what happens when there ARE duplicates?

The `toFinset` function **deduplicates**: it silently drops copies of
elements that already appear. Concretely, if `a` is already in list
`l`, then `(a :: l).toFinset = l.toFinset`. The extra `a` at the front
is discarded because `toFinset` already contains it.

The mechanism:
1. `List.toFinset_cons` gives `(a :: l).toFinset = insert a l.toFinset`
2. `Finset.insert_eq_of_mem` says: if `a` is already in a finset, inserting it changes nothing
3. `List.mem_toFinset` bridges list membership to finset membership

**Your task**: Prove that prepending a duplicate to a list doesn't
change its `toFinset`. This is deduplication made explicit.
"

/-- Adding a duplicate element to a list doesn't change its toFinset. -/
Statement (a : ℕ) (l : List ℕ) (h : a ∈ l) :
    (a :: l).toFinset = l.toFinset := by
  Hint "Start by unfolding the toFinset of the cons'd list using
  `List.toFinset_cons`."
  rw [List.toFinset_cons]
  Hint "The goal is `insert a l.toFinset = l.toFinset`. Since `a` is
  already in `l`, it's already in `l.toFinset`. Use
  `Finset.insert_eq_of_mem` to show the insert is redundant."
  Hint (hidden := true) "You need to show `a ∈ l.toFinset`.
  Try:
  `apply Finset.insert_eq_of_mem`
  `rw [List.mem_toFinset]`
  `exact h`"
  apply Finset.insert_eq_of_mem
  rw [List.mem_toFinset]
  exact h

Conclusion "
You proved that deduplication is idempotent: if an element is already
in the list, adding it again doesn't change the finset.

This is the concrete mechanism behind the gap between `length` and
`toFinset.card`:
- Each duplicate element triggers `insert_eq_of_mem` — the insert
  is silently absorbed
- The finset grows only when a genuinely new element appears

**Example**: Consider `[1, 2, 2, 3]`:
- `(1 :: [2, 2, 3]).toFinset = insert 1 ([2, 2, 3].toFinset)` — 1 is new, count goes up
- `(2 :: [2, 3]).toFinset = insert 2 ([2, 3].toFinset)` — 2 is already there, absorbed
- `(2 :: [3]).toFinset = insert 2 ([3].toFinset)` — 2 is new here, count goes up
- `(3 :: []).toFinset = insert 3 ∅` — 3 is new, count goes up

Result: 3 distinct elements from a length-4 list.

Next, you'll see this gap in action: a level where `length ≠ card`.
"

TheoremTab "List"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
