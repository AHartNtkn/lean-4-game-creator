import Game.Metadata

World "HomBasics"
Level 3

Title "Kernel Membership Practice"

Introduction
"
If `a` and `b` are both in `ker(f)`, what about `a * b`?

You know `f(a) = 1` and `f(b) = 1`. Push `f` through the product:
`f(a * b) = f(a) · f(b) = 1 · 1 = 1`.

This is the hom-property move combined with kernel reasoning:
unfold the kernel hypotheses, push `f` through, simplify.

The steps:
1. Unfold both kernel hypotheses with `rw [MonoidHom.mem_ker] at ha hb`
2. Push `f` through: `rw [map_mul]`
3. Substitute: `rw [ha, hb]`
4. Simplify: `rw [one_mul]` (or `exact one_mul 1`)
"

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem MulMemClass.mul_mem

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) (a b : G)
    (ha : a ∈ f.ker) (hb : b ∈ f.ker) : f (a * b) = 1 := by
  Hint "Unfold the kernel hypotheses first:
  `rw [MonoidHom.mem_ker] at {ha} {hb}`."
  rw [MonoidHom.mem_ker] at ha hb
  Hint "Now `{ha} : f a = 1` and `{hb} : f b = 1`. Push `f` through
  the product: `rw [map_mul]`."
  rw [map_mul]
  Hint "Substitute both: `rw [{ha}, {hb}]`."
  rw [ha, hb]
  Hint (hidden := true) "The goal is `1 * 1 = 1`. Use `rw [one_mul]`
  or `exact one_mul 1`."
  rw [one_mul]

Conclusion
"
The pattern is always the same:

1. Unfold `mem_ker` at the hypotheses → get `f x = 1`
2. Push `f` through with `map_mul` (or `map_inv`, `map_one`)
3. Substitute the `f x = 1` equations
4. Simplify the resulting group algebra

This is exactly proving that `f.ker` is closed under multiplication.
And indeed, `f.ker` is a `Subgroup G` — it satisfies all three
membership axioms (`one_mem`, `mul_mem`, `inv_mem`). You proved
`one_mem` in Level 1, and `mul_mem` just now.

In fact, for any `ha : a ∈ f.ker` and `hb : b ∈ f.ker`, you can
use `mul_mem ha hb` directly to get `a * b ∈ f.ker` — because
Lean already knows `f.ker` is a subgroup. But knowing *why* it
works matters more than the shortcut.
"
