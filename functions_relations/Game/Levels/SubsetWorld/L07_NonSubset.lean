import Game.Metadata

World "SubsetWorld"
Level 7

Title "Disproving a Subset"

Introduction "
# When ⊆ Fails: Proving ¬(s ⊆ t)

All the subset proofs so far have been **positive**: you showed that
one set is contained in another. But what if the containment is
**false**? How do you prove `¬(s ⊆ t)`?

In Lean, `¬ P` is defined as `P → False`. So to prove `¬(s ⊆ t)`,
you use `intro h` to **assume** the subset holds, getting
`h : s ⊆ t`, and then derive a contradiction (`False`).

To derive the contradiction, exhibit a **counterexample**: find an
element that is in `s` but not in `t`. If the subset held, this
element would have to be in both — but it is not, so we get `False`.

In Level 1, we noted that `{n | n < 5} ⊆ {n | n < 3}` is false
because 4 is in the first set but not the second. Now you will prove
this formally.

**Proof plan**:
1. `intro h` — assume the subset holds (goal becomes `False`)
2. Prove `4 ∈ {n | n < 5}` — show the witness is in the domain
3. Apply `h` to get `4 ∈ {n | n < 3}` — use the assumed subset
4. Unwrap and derive contradiction — `4 < 3` is false
"

/-- The set of numbers less than 5 is NOT a subset of the set of
numbers less than 3. -/
Statement : ¬ ({n : ℕ | n < 5} ⊆ {n | n < 3}) := by
  Hint "The goal is `¬ (... ⊆ ...)`, which means `(... ⊆ ...) → False`.
  Use `intro h` to assume the subset holds and aim for a contradiction."
  intro h
  Hint "Now `h` says every number less than 5 is less than 3. This is
  false — 4 is less than 5 but not less than 3. First, prove that
  4 < 5: use `have h4 : (4 : ℕ) < 5 := by omega`.

  Since `4 ∈ (the left set)` is definitionally `4 < 5`, Lean will
  accept this as a membership proof."
  Hint (hidden := true) "Step by step:
  1. `have h4 : (4 : ℕ) < 5 := by omega`
  2. `have h4' := h h4`
  3. `change (4 : ℕ) < 3 at h4'`
  4. `omega`"
  have h4 : (4 : ℕ) < 5 := by omega
  Hint "Good — `h4 : 4 < 5` also serves as a proof that 4 is in the
  left set (since set membership unfolds to the predicate). Now apply
  the assumed subset to this witness: `have h4' := h h4`. This uses
  `h` as a function (just like Level 6)."
  have h4' := h h4
  Hint "`h4'` says 4 is in the right set, which is definitionally `4 < 3`.
  Unwrap it with `change (4 : ℕ) < 3 at h4'`, then `omega` sees the
  contradiction and closes the `False` goal."
  change (4 : ℕ) < 3 at h4'
  Hint "`h4' : 4 < 3` is clearly false. `omega` can derive `False`
  from contradictory arithmetic hypotheses."
  omega

Conclusion "
You just proved your first **negative** subset statement! The proof
structure was:

1. **Assume** the subset holds (`intro h`)
2. **Exhibit** a counterexample element (4)
3. **Apply** the assumed subset to the counterexample (`h h4`)
4. **Derive contradiction** from the impossible conclusion (`4 < 3`)

This is a **proof by counterexample**: to disprove a universal
statement `∀ x, P x`, you assume it holds and exhibit a specific
`x₀` where `P x₀` leads to a contradiction. Here, the universal
statement is `∀ x, x < 5 → x < 3`, and the counterexample is `x₀ = 4`.

This is a specific form of proof by contradiction, but the key
technique — **finding a witness that breaks the claim** — deserves its
own name. You will use proof by counterexample throughout this course:
to disprove injectivity (find two inputs with the same output), to
disprove surjectivity (find an output with no input), and to disprove
set equality (find an element in one set but not the other).

Notice how Step 3 used the subset-as-function pattern from Level 6:
`h h4` applies the subset hypothesis `h` to the membership proof
`h4`. The difference is that here, the conclusion is *absurd* — which
is exactly how we know the assumption was wrong.

In ordinary math: \"Suppose `{n | n < 5} ⊆ {n | n < 3}`. Then in
particular `4 < 3`, which is false. Contradiction.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.not_subset
