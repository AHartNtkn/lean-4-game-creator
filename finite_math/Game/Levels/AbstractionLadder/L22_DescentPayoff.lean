import Game.Metadata

World "AbstractionLadder"
Level 22

Title "Descending the Ladder"

Introduction "
# The Ladder in Action: Descending to Prove a Finset Fact

The world introduction promised: *when a finset proof is hard, you can
descend to the list or multiset level, use richer tools there, and
bring the result back up.*

Time to deliver on that promise.

**The setup**: You have two lists `l₁` and `l₂` whose concatenation
has no duplicates. You know each list's length.

**Your task**: Prove that `(l₁ ++ l₂).toFinset.card = 7`.

This is a statement about **finset cardinality** — but the most natural
proof works entirely at the **list level**:

1. **Descend**: Use `toFinset_card_of_nodup` to convert the finset
   card to a list length (since the concatenation has no duplicates)
2. **Use list tools**: Apply `List.length_append` to split the
   concatenated length into a sum
3. **Close**: Rewrite with the known lengths

The insight: finset cardinality is hard to compute directly, but list
length is easy. The `toFinset_card_of_nodup` bridge lets you work
where the tools are strongest.
"

/-- Descend to the list level to compute a finset cardinality. -/
Statement (l₁ l₂ : List ℕ) (hnd : (l₁ ++ l₂).Nodup)
    (h₁ : l₁.length = 3) (h₂ : l₂.length = 4) :
    (l₁ ++ l₂).toFinset.card = 7 := by
  Hint "Start by descending the ladder: use `List.toFinset_card_of_nodup`
  to convert finset cardinality to list length.
  The hypothesis `hnd` provides the nodup condition."
  Hint (hidden := true) "Try `rw [List.toFinset_card_of_nodup hnd]`."
  rw [List.toFinset_card_of_nodup hnd]
  Hint "Now you're at the list level. The goal is
  `(l₁ ++ l₂).length = 7`. Use `List.length_append` to split the
  concatenation length into a sum."
  rw [List.length_append]
  Hint "The goal is `l₁.length + l₂.length = 7`. Rewrite with the
  known lengths."
  Hint (hidden := true) "Try `rw [h₁, h₂]`."
  rw [h₁, h₂]

Conclusion "
You just used the abstraction ladder as a **proof tool**:

1. The question was about finset cardinality (top layer)
2. You descended to list length via `toFinset_card_of_nodup`
3. You used `length_append` — a list-level tool — to finish

This is the pattern the world has been building toward: when the
finset layer doesn't have the right tools, descend to where the
tools are richer, solve the problem there, and let the bridge lemmas
carry the result back up.

**When to use this strategy**: Whenever you see `l.toFinset.card`
and the list `l` is built from known components (cons, append,
specific lists), ask: 'Is this easier to compute as a list length?'
If `l` has no duplicates, `toFinset_card_of_nodup` lets you do
exactly that.
"

TheoremTab "List"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
