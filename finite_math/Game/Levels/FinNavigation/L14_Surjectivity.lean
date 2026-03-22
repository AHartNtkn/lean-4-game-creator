import Game.Metadata

World "FinNavigation"
Level 14

Title "castSucc Surjectivity"

Introduction "
# Every Non-Last Element is a castSucc Image

In Level 7, you proved that no `castSucc` image equals `Fin.last`.
This level proves the **converse**: if an element is NOT `Fin.last`,
then it IS a `castSucc` image. Together, they give an exact
characterization: *an element of `Fin (n+1)` is a `castSucc`
image if and only if it is not `Fin.last n`*.

This completes the embedding picture for `castSucc`:
- **Injectivity** (Level 8): different inputs give different outputs
- **Separation** (Level 7): no output equals `Fin.last`
- **Surjectivity** (this level): every non-`last` element IS an output (converse of L7)

Together: `castSucc` is a *bijection* between `Fin n` and
`Fin (n+1) minus the last element`.

**Strategy**:
1. Derive `i.val /= n` from `i /= Fin.last n`
2. Use `omega` to get `i.val < n` (from `i.val < n + 1` and `i.val /= n`)
3. Provide the witness `(i.val, proof)` and prove equality via `ext`
"

/-- Every element not equal to `Fin.last` is a `castSucc` image. -/
Statement (n : ℕ) : ∀ i : Fin (n + 1), i ≠ Fin.last n → ∃ j : Fin n, i = j.castSucc := by
  Hint "Start with `intro i hne`."
  intro i hne
  Hint "First derive that `i.val /= n`. Use a `have` block:
  assume `i.val = n`, then show `i = Fin.last n` (contradicting `hne`)."
  Hint (hidden := true) "`have hval : i.val /= n := by`
  then inside: `intro heq; apply hne; ext; rw [Fin.val_last]; exact heq`"
  have hval : i.val ≠ n := by
    intro heq
    apply hne
    ext
    rw [Fin.val_last]
    exact heq
  Hint "Now `i.val < n + 1` (from `i.isLt`) and `i.val /= n`
  together give `i.val < n`. Provide the witness."
  Hint (hidden := true) "`use ⟨i.val, by omega⟩; ext; rw [Fin.val_castSucc]`"
  use ⟨i.val, by omega⟩
  ext
  rw [Fin.val_castSucc]

Conclusion "
The surjectivity proof introduced a new technique: **deriving a
value-level fact from a Fin-level hypothesis**. You turned
`i /= Fin.last n` into `i.val /= n` by showing the contrapositive:
if the values were equal, `ext` would force the Fin elements to be
equal, contradicting the hypothesis.

This level and Level 7 together give the **if-and-only-if**:

> `i` is a `castSucc` image **iff** `i /= Fin.last n`

Level 7 proved the forward direction (castSucc images are never
last). This level proved the converse (non-last elements are always
castSucc images). Asking 'is the converse true?' is a fundamental
mathematical habit — and here the answer is yes.

With injectivity, separation, and surjectivity, the castSucc/last
decomposition is now fully justified:
- **Exhaustion**: every `i` is either `last` or `j.castSucc` (boss)
- **Disjointness**: no `castSucc` image equals `last` (Level 7)
- **Completeness**: every non-`last` element IS a `castSucc` image (this level)

In algebraic language, `castSucc` is an isomorphism between `Fin n`
and the complement of the last element in `Fin (n+1)`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem Fin.lastCases Fin.reverseInduction
