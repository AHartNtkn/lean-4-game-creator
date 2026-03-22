import Game.Metadata

World "FinNavigation"
Level 12

Title "Recognizing the Last Element"

Introduction "
# When is an Element Fin.last?

In Level 7, you proved that `castSucc` images can never equal
`Fin.last`. The converse question: if you *know* an element's
value equals `n`, can you conclude it IS `Fin.last n`?

Yes. Two `Fin` elements are equal when their values are equal
(`ext` from the previous world). So if `i.val = 3` and
`(Fin.last 3).val = 3`, then `i = Fin.last 3`.

**Strategy**:
1. `intro i h` — introduce the element and hypothesis
2. `ext` — reduce `i = Fin.last 3` to `i.val = (Fin.last 3).val`
3. `rw [Fin.val_last]` — simplify RHS to `3`
4. `exact h` — the hypothesis gives `i.val = 3`
"

/-- An element with value `n` equals `Fin.last n`. -/
Statement : ∀ i : Fin 4, i.val = 3 → i = Fin.last 3 := by
  Hint "Start with `intro i h`."
  intro i h
  Hint "Use `ext` to reduce the equality to values."
  ext
  Hint "Use `rw [Fin.val_last]` to simplify `(Fin.last 3).val` to `3`."
  rw [Fin.val_last]
  Hint "The goal is `i.val = 3`, which is exactly `{h}`."
  exact h

Conclusion "
The pattern for recognizing `Fin.last`:
```
ext; rw [Fin.val_last]; ...
```

This converts `i = Fin.last n` into `i.val = n`, which you can
close with a hypothesis or `omega`.

In the boss, you'll use this pattern inside a case analysis: when
the case split gives you the maximum value, you'll identify the
element as `Fin.last` using exactly this recipe.

The mirror image — recognizing a `castSucc` image — is next.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
