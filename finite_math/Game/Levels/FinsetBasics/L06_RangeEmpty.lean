import Game.Metadata

World "FinsetBasics"
Level 6

Title "The Empty Range"

Introduction "
# Finset.range 0 is Empty

In MeetFin, you proved that `Fin 0` has no elements — no natural
number is less than 0. The same fact holds for `Finset.range 0`:
it contains no members, because `Finset.range 0` is the set of
natural numbers less than 0.

Level 4's conclusion mentioned this boundary case. Now you'll prove
it: no natural number belongs to `Finset.range 0`.

**Strategy**: The non-membership pattern from Level 5:
1. `intro x` — introduce the element
2. `intro h` — assume `h : x ∈ Finset.range 0`
3. `rw [Finset.mem_range] at h` — converts to `h : x < 0`
4. `omega` — contradiction (no natural number is less than 0)
"

/-- No natural number belongs to Finset.range 0. -/
Statement : ∀ x : ℕ, x ∉ Finset.range 0 := by
  Hint "Introduce `x` and assume membership: `intro x h`."
  intro x h
  Hint "Now rewrite the membership: `rw [Finset.mem_range] at h`.
  This gives `h : x < 0`."
  rw [Finset.mem_range] at h
  Hint "No natural number is less than 0. `omega` sees the
  contradiction."
  omega

Conclusion "
`Finset.range 0` is empty — it has no members. This directly
parallels `Fin 0` being empty (MeetFin Level 13): both facts come
from the same arithmetic truth that no natural number is less than 0.

| Phase 1 | Phase 2 |
|---|---|
| `Fin 0` is empty (no inhabitants) | `Finset.range 0` is empty (no members) |
| `i.isLt` gives `i.val < 0` — impossible | `mem_range` gives `x < 0` — impossible |

This is the boundary case of `Finset.range n`. For `n = 0`, the
range is empty. For `n >= 1`, the range has `n` elements:
`{0, 1, ..., n-1}`.

The equality `Finset.range 0 = ∅` (which follows from what you just
proved) will be useful later when you encounter base cases of
induction on finset ranges.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.not_mem_range_self
