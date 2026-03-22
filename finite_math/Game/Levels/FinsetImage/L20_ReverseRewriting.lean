import Game.Metadata

World "FinsetImage"
Level 20

Title "Reverse Rewriting with ←"

Introduction "
# The `←` Modifier for `rw`

So far, every `rw` you've used rewrites **left to right**: if
`h : A = B`, then `rw [h]` replaces `A` with `B` in the goal.

But sometimes you need the **reverse direction**: replace `B`
with `A`. The `←` modifier does this:

- `rw [h]` — rewrites left to right: replaces `A` with `B`
- `rw [← h]` — rewrites right to left: replaces `B` with `A`

Type `←` as `\\l` (backslash-l).

**Why this matters**: Many Mathlib lemmas are stated as
`A ↔ B`, but your goal matches `B` and you need to convert
it to `A`. For example, `Finset.card_image_iff` states:
```
(s.image f).card = s.card ↔ Set.InjOn f ↑s
```

In Level 18, you used forward `rw` on a *hypothesis*:
`rw [Finset.card_image_iff] at hcard` converted a cardinality
equation (left side) into an injectivity statement (right side).

Now you'll use `← rw` on the *goal*: if your goal is
`Set.InjOn f ↑s` (the right side), then
`rw [← Finset.card_image_iff]` converts it to
`(s.image f).card = s.card` (the left side).

**Your task**: Given that the image preserves cardinality, prove
that `f` is injective on `s`. Convert the injectivity goal to a
cardinality equation using `← rw`, then close with the hypothesis.
"

/-- Reverse rewriting converts between equivalent formulations. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hcard : (s.image f).card = s.card) :
    Set.InjOn f ↑s := by
  Hint "Your goal is `Set.InjOn f ↑s` — the RIGHT side of
  `Finset.card_image_iff`. Use `rw [← Finset.card_image_iff]`
  to convert it to `(s.image f).card = s.card` (the LEFT side)."
  rw [← Finset.card_image_iff]
  Hint "Now the goal is `(s.image f).card = s.card`, which
  matches the hypothesis `hcard` exactly."
  Hint (hidden := true) "`exact hcard`"
  exact hcard

Conclusion "
You've learned the `←` modifier for `rw`:

- `rw [h]` replaces the LEFT side with the RIGHT side
- `rw [← h]` replaces the RIGHT side with the LEFT side

This works for both equalities (`=`) and biconditionals (`↔`).

**Comparison with Level 18**: In Level 18, you used forward `rw`
on a hypothesis to convert FROM cardinality TO injectivity. Here
you used reverse `rw` on the goal to convert FROM injectivity
TO cardinality. Same lemma, opposite direction, different target
(hypothesis vs. goal). The `←` gives you full flexibility.

The `←` modifier is essential when:
- A lemma is stated as `A ↔ B` but your goal matches `B`
  (you want to convert to `A`)
- A lemma is stated as `A = B` but your goal contains `B`
  (you want to go back to `A`)

In the next level, you'll see `← rw` used as a proof technique:
converting an injectivity goal into a cardinality equation that
Lean can verify computationally.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono Finset.card_image_of_injOn
