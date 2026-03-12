import Game.Metadata

World "GroupTutorial"
Level 2

Title "Left Identity"

Introduction
"
Now meet the second identity axiom: `one_mul` says `1 * a = a`.

Notice the naming convention: in `mul_one`, the `1` appears on the **right**
(`a * 1`). In `one_mul`, the `1` appears on the **left** (`1 * a`).
The name tells you which side the identity is on.

This time, the goal has **both** patterns: there's a `1 *` on the left
and a `* 1` on the right. You'll need two rewrites.
"

/-- `one_mul` says `1 * a = a` for any element `a` of a group.

Use it with `rw [one_mul]` when you see `1 * _` in the goal.

Don't confuse with `mul_one`, which handles `_ * 1`. -/
TheoremDoc one_mul as "one_mul" in "Group"

NewTheorem one_mul

TheoremTab "Group"

Statement (G : Type*) [Group G] (a : G) : 1 * a * 1 = a := by
  Hint "The goal is `1 * a * 1 = a`. Remember, this is left-associated:
  it means `(1 * a) * 1 = a`. You need to remove both identity elements.
  Try starting with `rw [one_mul]`."
  Branch
    rw [mul_one]
    Hint "Now you have `1 * a = a`. Which axiom handles `1 * _`?"
    rw [one_mul]
  rw [one_mul]
  Hint "After removing `1 *` from the left, you should see `a * 1 = a`.
  You've seen this before — this is `mul_one`."
  rw [mul_one]

Conclusion
"
Notice the asymmetry: `mul_one` handles `a * 1` and `one_mul` handles
`1 * a`. The names follow a convention — the identity appears in the
position named by the prefix. We'll see more axioms with this naming
pattern.

You can apply the rewrites in either order. Both `rw [one_mul, mul_one]`
and `rw [mul_one, one_mul]` work here.

(Mathematically, `one_mul` is not an independent axiom — it can be
*derived* from `mul_one`, `mul_inv_cancel`, and `mul_assoc`. We'll
prove this derivation in the next world.)
"
