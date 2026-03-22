import Game.Metadata

World "MeetFin"
Level 7

Title "Rewriting Hypotheses"

Introduction "
# Rewriting Hypotheses with `at`

In Level 5, you used `rw [Fin.ext_iff]` to rewrite the **goal**.
But `rw` can also rewrite **hypotheses**. The syntax is:
```
rw [Fin.ext_iff] at h
```
This converts a hypothesis `h : i = j` into `h : i.val = j.val`.

Here you have `h : i = j` (a `Fin` equality) and `p : i.val < 3`.
The goal asks for `j.val < 3`. Notice that `p` mentions `i.val`
but the goal mentions `j.val`.

Strategy: use `rw [Fin.ext_iff] at h` to extract the value equality,
then `omega` can combine `h` and `p` to close the goal.
"

/-- Transfer a bound through a Fin equality. -/
Statement (i j : Fin 5) (h : i = j) (p : i.val < 3) : j.val < 3 := by
  Hint "Use `rw [Fin.ext_iff] at h` to convert `{h}` from
  a `Fin` equality to a value equality `i.val = j.val`."
  rw [Fin.ext_iff] at h
  Hint "Now `{h}` says `i.val = j.val` and `{p}` says `i.val < 3`.
  `omega` can combine these to conclude `j.val < 3`."
  omega

Conclusion "
You now know both directions of `Fin.ext_iff`:

| Direction | Syntax | Effect |
|---|---|---|
| Goal: `i = j` → `i.val = j.val` | `rw [Fin.ext_iff]` | Reduces Fin equality to value equality |
| Hypothesis: `h : i = j` → `h : i.val = j.val` | `rw [Fin.ext_iff] at h` | Extracts value equality from Fin equality |

The `at h` modifier works with any `rw` — not just `Fin.ext_iff`.
Whenever you want to rewrite a hypothesis instead of the goal,
add `at h` (where `h` is the hypothesis name).
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
