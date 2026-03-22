import Game.Metadata

World "PsetFin"
Level 15

Title "Obtain Meets Decomposition"

Introduction "
# Combining obtain with Decomposition

In Level 8, you learned `obtain` for destructuring existentials.
In Levels 11-12, you proved general decompositions that produce
existential results (`exists j, i = j.castSucc`).

Here you'll combine them: given that an element is a `castSucc`
image, use `obtain` to extract the preimage, then prove the
element can't be `Fin.last`.

This is the **converse** of FinNavigation Level 14 (surjectivity):
there you proved `i /= last -> exists j, i = j.castSucc`. Here
you prove `exists j, i = j.castSucc -> i /= last`.

**Strategy**:
1. `obtain` the witness from the existential
2. Rewrite using the equation
3. Apply the value-reasoning pattern from FinNavigation L07
"

/-- A castSucc image is never the last element. -/
Statement (n : ℕ) (i : Fin (n + 1)) (h : ∃ j : Fin n, i = j.castSucc) :
    i ≠ Fin.last n := by
  Hint "Destructure the existential: `obtain ⟨j, hj⟩ := h`.
  This gives you the preimage `j` and the equation `hj`."
  obtain ⟨j, hj⟩ := h
  Hint "Rewrite `i` using the equation: `rw [hj]`.
  Now the goal is `j.castSucc /= Fin.last n`."
  rw [hj]
  Hint "This is the separation fact from FinNavigation L07, now
  for general `n`. Assume equality and derive a contradiction
  via value reasoning."
  Hint (hidden := true) "`intro heq; rw [Fin.ext_iff] at heq;
  rw [Fin.val_castSucc, Fin.val_last] at heq; omega`"
  intro heq
  rw [Fin.ext_iff] at heq
  rw [Fin.val_castSucc, Fin.val_last] at heq
  omega

Conclusion "
You combined two skills:
1. **`obtain`** to destructure the existential hypothesis
2. **Value reasoning** (ext_iff + val lemmas + omega) to derive
   the contradiction

This is a common pattern in real Lean proofs: a previous result
gives you an existential (`exists j, i = j.castSucc`), and you
need to destructure it with `obtain` before you can use the
equation. The value repackaging goes in reverse here — instead
of constructing a witness, you're unpacking one that was given.

The fact you just proved — castSucc images are never last — is
the converse of the surjectivity result from FinNavigation L14:
non-last elements are always castSucc images. Together they say:
an element is a castSucc image *if and only if* it's not last.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext Fin.castSucc_ne_last Fin.castSucc_lt_last Fin.lastCases Fin.reverseInduction
