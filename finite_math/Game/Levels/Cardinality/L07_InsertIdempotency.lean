import Game.Metadata

World "Cardinality"
Level 7

Title "Insert Doesn't Always Add One"

Introduction "
# When Insert is a No-Op

In Level 6, you learned `card_insert_of_notMem`: inserting a NEW
element adds 1 to the cardinality. But what if the element is
ALREADY in the set?

You proved in FinsetBasics that `Finset.insert_eq_of_mem`:
if `a \\in s`, then `insert a s = s` — insert is a no-op.

The cardinality consequence: if `a \\in s`, then
`(insert a s).card = s.card` — the count doesn't change.

This addresses a natural misconception: `card(insert a s) = card s + 1`
is NOT always true. It's only true when `a \\notin s`. When `a \\in s`,
the cardinality stays the same because insert is idempotent.

**Your task**: Given `a \\in s`, prove that `(insert a s).card = s.card`.
"

/-- Inserting an existing element doesn't change cardinality. -/
Statement (s : Finset ℕ) (a : ℕ) (ha : a ∈ s) :
    (insert a s).card = s.card := by
  Hint "Since `a \\in s`, we know `insert a s = s` by
  `Finset.insert_eq_of_mem`. Rewrite the goal using this."
  Hint (hidden := true) "`rw [Finset.insert_eq_of_mem ha]`"
  rw [Finset.insert_eq_of_mem ha]

Conclusion "
One line — but the insight matters.

`card_insert_of_notMem` says: if `a \\notin s`, then
`(insert a s).card = s.card + 1`.

`insert_eq_of_mem` says: if `a \\in s`, then
`insert a s = s` (and therefore their cardinalities are equal).

Together: inserting `a` either adds 1 (if `a` is new) or does
nothing (if `a` already exists). There's no middle case. This is
why the non-membership hypothesis in `card_insert_of_notMem` is
essential — without it, you can't conclude the `+ 1`.

**The takeaway**: Always check `a \\in s` vs `a \\notin s` before
applying `card_insert_of_notMem`. The wrong assumption leads to
an off-by-one error.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
