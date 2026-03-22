import Game.Metadata

World "MeetFin"
Level 6

Title "The Converse Direction"

Introduction "
# Fin Equality Implies Value Equality

In Level 5, you proved that equal values imply equal `Fin` elements
(the backward direction of `Fin.ext_iff`).

The converse is also true: if two `Fin` elements are equal, then
their values are equal. This follows from a basic principle: applying
a function to both sides of an equality preserves the equality. Since
`.val` is a function from `Fin n` to `ℕ`, if `i = j` then
`i.val = j.val`.

In Lean, the simplest proof uses `rw` directly. If `h : i = j`, then
`rw [h]` replaces `i` with `j` in the goal, turning `i.val = j.val`
into `j.val = j.val` — which closes by reflexivity.

**Your task**: Prove that `Fin` equality implies value equality.
"

/-- If two `Fin` elements are equal, their values are equal. -/
Statement (i j : Fin 5) (h : i = j) : i.val = j.val := by
  Hint "You have `{h}` saying `i = j`. Use `rw [h]` to replace `i`
  with `j` in the goal."
  Hint (hidden := true) "`rw [h]` turns the goal into `j.val = j.val`,
  which Lean closes automatically."
  rw [h]

Conclusion "
Both directions of `Fin.ext_iff` are now concrete:

| Direction | Statement | Proof |
|---|---|---|
| Values → Elements | `i.val = j.val → i = j` | `rw [Fin.ext_iff]; exact h` |
| Elements → Values | `i = j → i.val = j.val` | `rw [h]` |

Together, they say: **`Fin` equality is completely determined by
value equality.** The type-level wrapper carries no extra
information beyond the natural number inside.

**The congruence principle**: The proof pattern here — if `h : i = j`
then `rw [h]` turns `i.val` into `j.val` — is an instance of a
general fact: *applying any function to both sides of an equality
preserves the equality*. If `h : a = b` and `f` is any function,
then `f a = f b`. In Lean, `rw [h]` handles this automatically.
This principle (called `congr_arg` in Lean's library) will appear
whenever you transfer an equality through a function.

*Term-mode alternative*: If you ever need `i.val = j.val` from
`h : i = j` as a standalone term (not via rewriting), Lean provides
`congrArg Fin.val h`. This says: apply the function `Fin.val` to
both sides of `h`. You won't need this in tactic proofs (where `rw`
handles it), but it's the general pattern behind what `rw` does.

In the next level, you'll learn to rewrite hypotheses (not just the
goal) using `rw [...] at h`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
