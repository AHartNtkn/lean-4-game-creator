import Game.Metadata

World "HomBasics"
Level 7

Title "Trivial Kernel Implies Equal Outputs"

Introduction
"
Now the other direction: if `ker(f) = ⊥` and `f(a) = f(b)`, then `a = b`.

The chain of reasoning:
- `a = b` ← `a * b⁻¹ = 1` ← `a * b⁻¹ ∈ ⊥` ← `a * b⁻¹ ∈ ker(f)` ← `f(a * b⁻¹) = 1`

You'll work backwards from the goal, transforming it step by step:

1. `rw [← mul_inv_eq_one]` — change `a = b` to `a * b⁻¹ = 1`
2. `rw [← Subgroup.mem_bot]` — change to `a * b⁻¹ ∈ ⊥`
3. `rw [← hk]` — change to `a * b⁻¹ ∈ f.ker` (using `hk : f.ker = ⊥`)
4. `rw [MonoidHom.mem_ker]` — change to `f (a * b⁻¹) = 1`
5. Then push `f` through and use `hab : f a = f b`
"

/-- `mul_inv_eq_one` says:

`a * b⁻¹ = 1 ↔ a = b`

This converts between \"the ratio is trivial\" and \"the elements
are equal\". Use `rw [← mul_inv_eq_one]` to change a goal `a = b`
into `a * b⁻¹ = 1`, or `rw [mul_inv_eq_one]` for the other direction. -/
TheoremDoc mul_inv_eq_one as "mul_inv_eq_one" in "Group"

NewTheorem mul_inv_eq_one

TheoremTab "Hom"

/-- Disabled — you will prove this yourself in the boss level. -/
TheoremDoc MonoidHom.ker_eq_bot_iff as "MonoidHom.ker_eq_bot_iff" in "Hom"

DisabledTactic simp group
DisabledTheorem MonoidHom.ker_eq_bot_iff injective_iff_map_eq_one injective_iff_map_eq_one'

Statement (G H : Type*) [Group G] [Group H] (f : G →* H)
    (hk : f.ker = ⊥) (a b : G) (hab : f a = f b) : a = b := by
  Hint "The goal is `a = b`. Transform it to `a * b⁻¹ = 1` using
  `rw [← mul_inv_eq_one]`."
  rw [← mul_inv_eq_one]
  Hint "Now convert `a * b⁻¹ = 1` to membership in `⊥`:
  `rw [← Subgroup.mem_bot]`."
  rw [← Subgroup.mem_bot]
  Hint "Now replace `⊥` with `f.ker` using `{hk}`:
  `rw [← {hk}]`."
  rw [← hk]
  Hint "Now unfold kernel membership:
  `rw [MonoidHom.mem_ker]`."
  rw [MonoidHom.mem_ker]
  Hint "The goal is `f (a * b⁻¹) = 1`. Push `f` through:
  `rw [map_mul]`, then `rw [map_inv]`."
  rw [map_mul]
  rw [map_inv]
  Hint "Now substitute `{hab} : f a = f b`:
  `rw [{hab}]`."
  rw [hab]
  Hint (hidden := true) "The goal is `f b * (f b)⁻¹ = 1`.
  Use `exact mul_inv_cancel (f b)`."
  exact mul_inv_cancel (f b)

Conclusion
"
That was the longest rewrite chain so far. Here's the full picture:

```
a = b
  ← a * b⁻¹ = 1          (mul_inv_eq_one)
  ← a * b⁻¹ ∈ ⊥          (mem_bot)
  ← a * b⁻¹ ∈ ker(f)     (ker = ⊥)
  ← f(a * b⁻¹) = 1       (mem_ker)
  ← f(a) · f(b)⁻¹ = 1    (map_mul, map_inv)
  ← f(b) · f(b)⁻¹ = 1    (hab)
  ✓                        (mul_inv_cancel)
```

This is the **forward direction** of the boss theorem:
*trivial kernel → injective*.

On paper: *\"Since `f(a) = f(b)`, we have
`f(ab⁻¹) = f(a)f(b)⁻¹ = 1`, so `ab⁻¹ ∈ ker(f) = {1}`,
hence `ab⁻¹ = 1`, so `a = b`.\"*
"
