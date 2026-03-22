import Game.Metadata

World "PsetFin"
Level 10

Title "Modular Equality"

Introduction "
# When Different Formulas Agree

Two functions on `Fin 5` are described by different-looking formulas:
- `f i = i + 3`
- `g i = i + 8`

Are they the same function? In ordinary arithmetic, adding 3 and
adding 8 give different results. But in `Fin 5`, the arithmetic wraps
around: `8 mod 5 = 3`, so `(8 : Fin 5) = (3 : Fin 5)`. This means
`i + 8 = i + 3` for every `i : Fin 5`.

**Your task**: Prove `f = g` using `ext` and the formula rewrites.
"

/-- Two functions with the same modular formula are equal. -/
Statement (f g : Fin 5 → Fin 5)
    (hf : ∀ i : Fin 5, f i = i + 3)
    (hg : ∀ i : Fin 5, g i = i + 8) : f = g := by
  Hint "Show the functions agree at every index.
  Use `ext i` to introduce the index."
  ext i
  Hint "Substitute both formulas: `rw [hf, hg]`.
  The resulting equality holds because `(3 : Fin 5) = (8 : Fin 5)`
  by modular arithmetic."
  Hint (hidden := true) "After `rw [hf, hg]`, the goal becomes
  `i + 3 = i + 8` in `Fin 5`. Since `(8 : Fin 5) = (3 : Fin 5)`
  by modular arithmetic, `rfl` closes it."
  rw [hf, hg]
  Hint (hidden := true) "Both sides are definitionally equal because
  `(8 : Fin 5) = (3 : Fin 5)`. Use `rfl`."
  rfl

Conclusion "
After rewriting, the goal was `i + 3 = i + 8` in `Fin 5`. This is
true by `rfl` because `(8 : Fin 5)` and `(3 : Fin 5)` are the
**same element** — `8 mod 5 = 3`.

This combines three skills:
- **Function extensionality** (`ext`) from FinTuples
- **Universally quantified rewrite** (`rw [hf, hg]`) from FinTuples
- **Modular arithmetic** from MeetFin Level 19

**Why does `rfl` close `i + 3 = i + 8` in `Fin 5`?** The numerals
`3` and `8` in `Fin 5` are *the same element*: both reduce to the
element with value `3` (since `8 mod 5 = 3`). Lean computes this
reduction during elaboration, so the two sides are definitionally
equal — no proof step required. This is the power of modular
arithmetic being built into the type: Lean *knows* that `(8 : Fin 5)`
and `(3 : Fin 5)` are identical.

In a pset, recognizing which skills to combine is the real challenge.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
