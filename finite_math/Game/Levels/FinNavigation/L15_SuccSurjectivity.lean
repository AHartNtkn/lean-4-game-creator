import Game.Metadata

World "FinNavigation"
Level 15

Title "succ Surjectivity"

Introduction "
# Every Non-Zero Element is a succ Image

In Level 14, you proved that `castSucc` surjects onto non-last elements:
if `i /= Fin.last n`, then `i` is a `castSucc` image.

Here is the **dual**: if `i /= 0`, then `i` is a `succ` image.
Just as every non-last element has a `castSucc` preimage, every
non-zero element has a `succ` preimage.

This completes the embedding picture for `succ`:
- **Injectivity** (Level 9): different inputs give different outputs
- **Separation** (Level 11): no output equals `0`
- **Surjectivity** (this level): every non-`0` element IS an output

Together: `succ` is a *bijection* between `Fin n` and
`Fin (n+1) minus the zero element`.

**Strategy**:
1. Destructure `i` as `⟨v, hv⟩`
2. Case-split on `v`: zero is ruled out by `i /= 0`
3. For `v = k + 1`, the witness is `⟨k, proof⟩`
"

/-- Every element not equal to `0` is a `succ` image. -/
Statement (n : ℕ) : ∀ i : Fin (n + 1), i ≠ 0 → ∃ j : Fin n, i = j.succ := by
  Hint "Start with `intro i hne`."
  intro i hne
  Hint "Destructure `i` into its value and bound:
  `cases i with | mk v hv`"
  cases i with
  | mk v hv =>
  Hint "Case-split on `v`: `cases v with | zero | succ k`"
  cases v with
  | zero =>
    Hint "Here `v = 0`, so `⟨0, hv⟩ = 0` — contradicting `hne`.
    Use `exact absurd rfl hne`."
    exact absurd rfl hne
  | succ k =>
    Hint "Here `v = k + 1`. The witness is `⟨k, proof⟩ : Fin n`
    where `k < n` follows from `k + 1 < n + 1`."
    Hint (hidden := true) "`use ⟨k, by omega⟩; ext; rw [Fin.val_succ]`"
    use ⟨k, by omega⟩
    ext
    rw [Fin.val_succ]

Conclusion "
You've proved the dual of Level 14: every non-zero element of
`Fin (n+1)` is a `succ` image.

The two surjectivity facts complete the dual decomposition picture:

| Decomposition | Surjectivity | Separation |
|---|---|---|
| castSucc/last | Non-last elements are castSucc images (L14) | castSucc never reaches last (L7) |
| 0/succ | Non-zero elements are succ images (this level) | succ never reaches 0 (L11) |

Both decompositions are now **fully justified**: exhaustion (every
element falls into one side), disjointness (no element falls into
both), and surjectivity (the non-boundary side is exactly the image
of the embedding).

The proof used a different technique than Level 14: instead of
deriving a value inequality and using subtraction, you destructured
`i` and case-split on the value directly. For `v = 0`, the hypothesis
`i /= 0` gives an immediate contradiction. For `v = k + 1`, the
witness `k` is right there — no subtraction needed.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem Fin.lastCases Fin.reverseInduction Fin.eq_zero_or_eq_succ Fin.cases
