import Game.Metadata

World "FinsetBasics"
Level 12

Title "Proving Non-membership"

Introduction "
# Proving Non-membership in a Literal Finset

In Level 5, you proved `5 ∉ Finset.range 5` by assuming membership
and reaching a contradiction. The same pattern works for literal
finsets.

To prove `4 ∉ {1, 2, 3}`:
1. `intro h` — assume `h : 4 ∈ {1, 2, 3}`
2. Unfold `h` completely: `rw [Finset.mem_insert, Finset.mem_insert,
   Finset.mem_singleton] at h` — this converts `h` to
   `4 = 1 ∨ 4 = 2 ∨ 4 = 3`
3. `omega` — all three disjuncts are false, so `omega` derives `False`

**Chained rewrites in a hypothesis**: You can chain multiple rewrites
in a single `rw [...] at h` — the same syntax you used for chained
rewrites on goals. This peels all the `insert`/`singleton` layers
at once.

**Why omega works on disjunctions**: `omega` reasons about linear
arithmetic over all hypotheses simultaneously. When every branch
of a disjunction leads to a false arithmetic statement, `omega`
sees the overall contradiction.
"

/-- 4 is not an element of {1, 2, 3}. -/
Statement : (4 : ℕ) ∉ ({1, 2, 3} : Finset ℕ) := by
  Hint "Assume membership: `intro h`."
  intro h
  Hint "Now unfold `{h}` completely. Chain the rewrites:
  `rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h`."
  Hint (hidden := true) "After the chained rewrite, `{h}` becomes
  `4 = 1 ∨ 4 = 2 ∨ 4 = 3`. Then `omega` closes the goal."
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
  Hint "Now `{h}` says `4 = 1 ∨ 4 = 2 ∨ 4 = 3`. All branches are
  false. `omega` derives the contradiction."
  omega

Conclusion "
Non-membership in a literal finset follows the same pattern as
non-membership in a range:

| Step | Range | Literal finset |
|---|---|---|
| Assume | `intro h` | `intro h` |
| Unfold | `rw [mem_range] at h` | `rw [mem_insert, ..., mem_singleton] at h` |
| Contradict | `omega` | `omega` |

The only difference is *how many* rewrites are needed. For a finset
with $k$ elements written as `insert a₁ (insert a₂ (... {aₖ}))`,
you need $k - 1$ `mem_insert` rewrites and one `mem_singleton` at
the end.

You now have both membership and non-membership proofs for
literal finsets.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
