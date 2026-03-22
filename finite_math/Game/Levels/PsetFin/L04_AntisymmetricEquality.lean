import Game.Metadata

World "PsetFin"
Level 4

Title "Antisymmetric Equality"

Introduction "
# When Two Inequalities Meet

You've used `ext` to prove Fin elements are equal by showing
their values are equal. Here's a twist: you know `i.val ≤ j.val`
AND `j.val ≤ i.val`. What can you conclude?

In ordinary math, if $a \\leq b$ and $b \\leq a$, then $a = b$.
This is the **antisymmetry** of `≤`. The same applies to Fin:
if the values are squeezed from both sides, they must be equal.

The proof technique is the same as always: reduce Fin equality
to value equality with `ext`, then let `omega` handle the
arithmetic.
"

/-- If both `i.val ≤ j.val` and `j.val ≤ i.val`, then `i = j`. -/
Statement (n : ℕ) (i j : Fin n) (h1 : i.val ≤ j.val) (h2 : j.val ≤ i.val) :
    i = j := by
  Hint "The goal is a Fin equality. What's the standard first move?"
  Hint (hidden := true) "Use `ext` to reduce to `i.val = j.val`,
  then `omega` combines the two inequalities."
  ext
  omega

Conclusion "
Two lines: `ext; omega`. But recognizing that `ext` is the right
first move is the real skill here.

Whenever you see `i = j` for Fin elements and you have
information about their values, `ext` converts the Fin equality
to a value equality where `omega` can work.

This is **antisymmetry**: `i.val ≤ j.val` and `j.val ≤ i.val`
together force `i.val = j.val`. In paper math you'd write:
$a \\leq b$ and $b \\leq a$ implies $a = b$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
