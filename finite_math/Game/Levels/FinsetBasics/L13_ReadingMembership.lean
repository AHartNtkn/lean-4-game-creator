import Game.Metadata

World "FinsetBasics"
Level 13

Title "Reading Membership"

Introduction "
# Reading Membership

So far, you've been *proving* membership: showing that a specific
element belongs to a finset. But sometimes you start with a
membership hypothesis and need to extract information from it.

If you know `h : x ∈ {1, 2, 3}`, what can you conclude about `x`?
Since `{1, 2, 3} = insert 1 (insert 2 {3})`, you can rewrite `h`
using the same membership lemmas — but at the hypothesis instead
of the goal:

```
rw [Finset.mem_insert] at h    -- h : x = 1 ∨ x ∈ {2, 3}
rw [Finset.mem_insert] at h    -- h : x = 1 ∨ x = 2 ∨ x ∈ {3}
rw [Finset.mem_singleton] at h -- h : x = 1 ∨ x = 2 ∨ x = 3
```

You can chain all three in one step:
`rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h`

This transforms a membership hypothesis into an explicit disjunction
listing the possible values of `x`. This is the **backward** direction
of finset membership — the counterpart to the forward direction you've
been practicing.

**Your task**: Given `h : x ∈ {1, 2, 3}`, prove `x = 1 ∨ x = 2 ∨ x = 3`.
"

/-- Membership in a literal finset means equality with one of the elements. -/
Statement (x : ℕ) (h : x ∈ ({1, 2, 3} : Finset ℕ)) : x = 1 ∨ x = 2 ∨ x = 3 := by
  Hint "Unfold the membership in `h` using
  `rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h`."
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
  Hint "Now `h` states exactly `x = 1 ∨ x = 2 ∨ x = 3`, which matches
  the goal. Close it with `exact h`."
  exact h

Conclusion "
You just used `Finset.mem_insert` in the **backward** direction:
starting from a membership hypothesis and unfolding it into a
disjunction of equalities.

| Direction | What you have | What you do |
|---|---|---|
| Forward (proving) | Goal: `x ∈ {{a, b, c}}` | `rw [mem_insert]` at goal, then `left`/`right` |
| Backward (reading) | Hyp: `h : x ∈ {{a, b, c}}` | `rw [mem_insert, ...] at h`, then use `h` |

This backward direction is essential for the next world. When you
need to prove a subset relation `s ⊆ t` (meaning `∀ x ∈ s, x ∈ t`),
you'll start with a membership hypothesis `h : x ∈ s` and need to
show `x ∈ t` — exactly the pattern you just practiced.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem
