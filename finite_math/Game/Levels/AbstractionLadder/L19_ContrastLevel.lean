import Game.Metadata

World "AbstractionLadder"
Level 19

Title "The Contrast: Length vs Card"

Introduction "
# What Each Layer Counts

Here's the full picture of the abstraction ladder, made concrete.

Consider a list with a repeated element. Its length counts
all entries, but its `toFinset.card` counts only distinct elements.

| Layer | Measure | `[1, 2, 2, 3]` |
|---|---|---|
| List | `.length` | 4 (all entries) |
| Multiset | `.card` | 4 (with multiplicity) |
| Finset | `.card` | 3 (distinct only) |

When a list has duplicates, `length > toFinset.card`. The gap is
exactly the number of duplicate occurrences.

**Your task**: Given a list whose length and toFinset card are known,
prove they are not equal.
"

/-- Duplicates cause list length and finset card to differ. -/
Statement (l : List ℕ) (hlen : l.length = 4) (hcard : l.toFinset.card = 3) :
    l.length ≠ l.toFinset.card := by
  Hint "Substitute the known values using `rw [hlen, hcard]`, then
  the goal becomes `4 ≠ 3`."
  rw [hlen, hcard]
  Hint "The goal is `4 ≠ 3`. Use `omega` to close it."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The key insight: list length and finset cardinality differ exactly when
the list has duplicates.

- **No duplicates** (`Nodup`): `l.toFinset.card = l.length` (as you
  proved with `toFinset_card_of_nodup`)
- **Has duplicates**: `l.toFinset.card < l.length` (the finset
  discards the extra copies)

This is the concrete meaning of the abstraction ladder:
- **List → Multiset**: forgets order (same count)
- **Multiset → Finset**: forgets duplicates (count can decrease)

Every time you use `Finset.card` in a proof, you're implicitly relying
on the fact that duplicates have been removed. The `Nodup` proof
inside every `Finset` is what makes this count meaningful.
"

TheoremTab "List"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
