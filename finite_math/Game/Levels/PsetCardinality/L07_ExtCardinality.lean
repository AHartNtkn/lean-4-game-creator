import Game.Metadata

World "PsetCardinality"
Level 7

Title "Extensionality and Cardinality"

Introduction "
# Same Elements, Same Size

You know that `s` and `t` have exactly the same elements
(`hst : ∀ x, x ∈ s ↔ x ∈ t`), and that `s.card = 8`.

**Your task**: Prove that `t.card = 8`.

The numbers are the same because the *sets* are the same.
How do you prove two finsets are equal from an element-wise
equivalence?
"

/-- Two finsets with the same elements have the same cardinality. -/
Statement (s t : Finset ℕ) (hst : ∀ x, x ∈ s ↔ x ∈ t) (hs : s.card = 8) :
    t.card = 8 := by
  Hint "You need `s = t` to transfer the cardinality fact. How do
  you prove two finsets are equal from element-wise equivalence?"
  Hint (hidden := true) "Use `ext` to prove the sets are equal:
  `have h : s = t := by ext x; exact hst x`"
  have h : s = t := by
    Hint "The goal is `s = t`. Use `ext x` to reduce to `x ∈ s ↔ x ∈ t`."
    Hint (hidden := true) "Try `ext x`."
    ext x
    Hint "`hst x` is exactly `x ∈ s ↔ x ∈ t`."
    exact hst x
  Hint "Good — you have `h : s = t`. Now transfer the cardinality."
  Hint (hidden := true) "Try `rw [← h]` to replace `t` with `s`, then `exact hs`."
  rw [← h]
  exact hs

Conclusion "
You proved that same elements implies same cardinality, by first
proving the sets are *equal*.

| Step | Move | What it does |
|---|---|---|
| 1 | `ext x` | reduces `s = t` to `x ∈ s ↔ x ∈ t` |
| 2 | `exact hst x` | closes the iff from the hypothesis |
| 3 | `rw [← h]` | substitutes `s` for `t` using equality |

The key retrieval: `ext` reduces set equality to element-wise
membership — the same tactic you learned in FinsetOperations.
Here you needed it *without being told* to use it. Recognizing
when `ext` is the right move is the skill being tested.

**Pattern**: When you have element-wise equivalence and need a
cardinality conclusion, first establish set equality via `ext`,
then substitute.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
