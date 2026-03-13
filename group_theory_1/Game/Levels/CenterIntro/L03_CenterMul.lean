import Game.Metadata

World "CenterIntro"
Level 3

Title "Products of Central Elements"

Introduction
"
If `a` and `b` are both in the center of `G`, is their product
`a * b` also in the center?

Yes — and the proof follows the same **unfold-intro-algebra** pattern
from Level 2, then uses the **shuttle argument** from the centralizer
world: move `g` through `a` using `ha`, then through `b` using `hb`,
reassociating with `mul_assoc` as needed.

Use a `calc` block to make each step visible.
"

TheoremTab "Center"

DisabledTactic group
DisabledTheorem MulMemClass.mul_mem

Statement (G : Type*) [Group G] (a b : G)
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center G) :
    a * b ∈ Subgroup.center G := by
  Hint "First, unfold center membership everywhere:
  `rw [Subgroup.mem_center_iff] at ha hb ⊢`

  This converts `ha`, `hb`, and the goal into their `∀ g, ...` forms."
  rw [Subgroup.mem_center_iff] at ha hb ⊢
  Hint "Now `intro g` to introduce the universal variable."
  intro g
  Hint "The goal is `g * ({a} * {b}) = {a} * {b} * g`. Sequential
  `rw` won't work well here — `rw [ha]` would look for `g * {a}` but
  the goal has `g * ({a} * {b})`. You need `← mul_assoc` first to
  re-associate.

  A `calc` block is the cleanest way to control each step. Shuttle
  `g` through `{a}` (using `ha`) and then through `{b}` (using `hb`).

  After the `rw` at `ha`, `ha` became `∀ (g : G), g * {a} = {a} * g`.
  This is a *function*: `ha g` gives `g * {a} = {a} * g`, and
  `rw [ha]` uses it to rewrite `g * {a}` to `{a} * g`. Similarly
  for `hb`.

  Use a `calc` block — same shuttle technique as the centralizer
  `mul_mem` proof from the Subgroup Definitions world:
  ```
  calc g * ({a} * {b})
      = g * {a} * {b}     := by rw [← mul_assoc]
    _ = ...
  ```"
  Hint (hidden := true) "Full `calc` proof:
  ```
  calc g * ({a} * {b})
      = g * {a} * {b}     := by rw [← mul_assoc]
    _ = {a} * g * {b}     := by rw [ha]
    _ = {a} * (g * {b})   := by rw [mul_assoc]
    _ = {a} * ({b} * g)   := by rw [hb]
    _ = {a} * {b} * g     := by rw [← mul_assoc]
  ```"
  calc g * (a * b)
      = g * a * b     := by rw [← mul_assoc]
    _ = a * g * b     := by rw [ha]
    _ = a * (g * b)   := by rw [mul_assoc]
    _ = a * (b * g)   := by rw [hb]
    _ = a * b * g     := by rw [← mul_assoc]

Conclusion
"
This is `mul_mem` for the center. The proof shape is the same as the
centralizer `mul_mem` proof from the Subgroup Definitions world, but
now the commuting hypotheses `ha` and `hb` are universal (`∀ g, ...`)
rather than specific to one element.

On paper: *\"Let `a, b ∈ Z(G)`. For any `g ∈ G`:
`g(ab) = (ga)b = (ag)b = a(gb) = a(bg) = (ab)g`,
so `ab ∈ Z(G)`.\"*

Each `=` corresponds to one `calc` step: re-associate, apply `ha`,
re-associate, apply `hb`, re-associate.
"
