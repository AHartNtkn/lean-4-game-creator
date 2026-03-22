import Game.Metadata

World "FinNavigation"
Level 13

Title "Finding a castSucc Preimage"

Introduction "
# When is an Element a castSucc Image?

If `i : Fin 4` has `i.val < 3`, then `i` must be `j.castSucc`
for some `j : Fin 3`. Why? Because `j.castSucc.val = j.val`,
so you can build the preimage `j` using the same value: take
`j := ⟨i.val, h⟩ : Fin 3` (where `h : i.val < 3`).

This requires a creative step: you must **construct** the
preimage yourself. The witness is `⟨i.val, h⟩` — the same
number, but viewed as living in the smaller type.

**Strategy**:
1. `intro i h`
2. `use ⟨i.val, h⟩` — provide the preimage
3. `ext` — reduce to value equality
4. `rw [Fin.val_castSucc]` — simplify `castSucc` value
"

/-- An element with value below `n` is a `castSucc` image. -/
Statement : ∀ i : Fin 4, i.val < 3 → ∃ j : Fin 3, i = j.castSucc := by
  Hint "Start with `intro i h`."
  intro i h
  Hint "The preimage is `⟨i.val, h⟩ : Fin 3` — the same number
  in the smaller type. Use `use ⟨i.val, h⟩`."
  use ⟨i.val, h⟩
  Hint "Now prove `i = (⟨i.val, h⟩).castSucc`. Use `ext` to
  reduce to values."
  ext
  Hint "Use `rw [Fin.val_castSucc]` to simplify `castSucc.val`
  to `i.val`."
  rw [Fin.val_castSucc]

Conclusion "
The pattern for finding a `castSucc` preimage:
```
use ⟨i.val, h⟩; ext; rw [Fin.val_castSucc]
```

The key insight: if you know `i.val < n`, then `⟨i.val, h⟩`
is a valid element of `Fin n`, and its `castSucc` has the same
value as `i`. Since two `Fin` elements with the same value are
equal (by `ext`), you're done.

This proof move deserves a name: **value repackaging**. You take
the same underlying value but justify it in a *different type* by
providing a new bound proof. The pattern is always:
`⟨i.val, new_bound_proof⟩`. You'll see value repackaging again
in the succ direction (building `⟨v - 1, ...⟩ : Fin n` from
`⟨v, ...⟩ : Fin (n + 1)`) and in the problem set when proving
general decomposition results. In the boss, you'll use this move
inside a case analysis, where the bound comes from the case split.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
