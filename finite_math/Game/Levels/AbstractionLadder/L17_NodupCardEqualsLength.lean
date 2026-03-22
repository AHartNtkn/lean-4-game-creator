import Game.Metadata

World "AbstractionLadder"
Level 17

Title "Nodup Lists: Card = Length"

Introduction "
# When Finset Card Equals List Length

Converting a list to a finset can lose elements (duplicates are removed).
But if the list has **no duplicates**, nothing is lost:

`List.toFinset_card_of_nodup h : l.toFinset.card = l.length`
  (from `h : l.Nodup`)

This is the precise statement: for a nodup list, the finset cardinality
equals the list length.

**Your task**: Given a nodup list of length 5, prove its toFinset has
card 5.
"

/-- For a nodup list, toFinset preserves the count. -/
Statement (l : List ℕ) (hnd : l.Nodup) (hlen : l.length = 5) :
    l.toFinset.card = 5 := by
  Hint "Use `List.toFinset_card_of_nodup` to connect finset card to
  list length, then rewrite with the length hypothesis."
  Hint (hidden := true) "Try:
  `rw [List.toFinset_card_of_nodup hnd]`
  `exact hlen`"
  rw [List.toFinset_card_of_nodup hnd]
  exact hlen

Conclusion "
`toFinset_card_of_nodup` is the key quantitative bridge: for nodup lists,
list length and finset card agree perfectly.

Without the nodup condition, the card can be strictly less. For example:
- `[1, 2, 2, 3].length = 4` but `[1, 2, 2, 3].toFinset.card = 3`

The nodup condition guarantees no duplicates are discarded, so nothing
is lost in the conversion.

**The complete picture**:
| Source | Measure | `[1, 2, 3]` | `[1, 2, 2, 3]` |
|---|---|---|---|
| List | `.length` | 3 | 4 |
| Multiset | `.card` | 3 | 4 |
| Finset | `.card` | 3 | 3 |

The first two always agree (coercion preserves count). The last agrees
with the others only when the list has no duplicates.
"

/-- `List.toFinset_card_of_nodup h` states that
`l.toFinset.card = l.length` when `h : l.Nodup`.

## Syntax
```
rw [List.toFinset_card_of_nodup hnd]
```

## When to use it
When you have a nodup list and need to connect finset cardinality
to list length.
-/
TheoremDoc List.toFinset_card_of_nodup as "List.toFinset_card_of_nodup" in "List"

TheoremTab "List"
NewTheorem List.toFinset_card_of_nodup

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
