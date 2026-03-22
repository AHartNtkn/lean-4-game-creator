import Game.Metadata

World "FinsetBasics"
Level 11

Title "The General Boundary"

Introduction "
# n is Never in Finset.range n

In Level 5, you proved `5 ∉ Finset.range 5` — the boundary element
is excluded from the range. That was a concrete instance.

Now prove the **general** version: for any `n`, `n` itself is not
in `Finset.range n`. This parallels MeetFin Level 12, where you
moved from `Fin 5` to `Fin (n + 1)` — the same skills work with
variables.

**Strategy**: The same non-membership pattern from Level 5, now
with a variable `n` instead of the concrete `5`.
"

/-- n is never a member of Finset.range n. -/
Statement (n : ℕ) : n ∉ Finset.range n := by
  Hint "Assume membership: `intro h`."
  intro h
  Hint "Rewrite to extract the inequality:
  `rw [Finset.mem_range] at h`."
  rw [Finset.mem_range] at h
  Hint "Now `{h}` says `n < n`, which is impossible. `omega`
  derives the contradiction."
  omega

Conclusion "
The general boundary exclusion: `n ∉ Finset.range n` for all `n`.

This is the `Finset.range` analog of MeetFin Level 3 (`x.val /= n`
for `x : Fin n`). Both say: the boundary value is excluded.

| Concrete (Level 5) | General (this level) |
|---|---|
| `5 ∉ Finset.range 5` | `n ∉ Finset.range n` |
| `5 < 5` is false | `n < n` is false |

The proof is identical — only the numbers changed from concrete to
variable. This transfer from concrete to abstract is a pattern
you'll keep seeing: prove a specific instance first to understand
the structure, then generalize.

The library name for this fact is `Finset.not_mem_range_self`. Now
that you've proved it manually, you understand *why* it's true:
`mem_range` converts to `n < n`, and strict inequality is irreflexive.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.not_mem_range_self
