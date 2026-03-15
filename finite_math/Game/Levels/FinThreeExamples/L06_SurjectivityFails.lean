import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 6

Title "Surjectivity fails: Fin 3 to Fin 4"

Introduction
"
# A Function from `Fin 3` to `Fin 4` Cannot Be Surjective

Can a function from `Fin 3` to `Fin 4` be surjective? Intuitively, no:
you have only 3 inputs but 4 outputs to cover. At least one output
must be missed.

This is a preview of the **pigeonhole principle**, which you will study
in a later world.

## The function

The canonical embedding `Fin.castSucc : Fin 3 → Fin 4` maps each
element to itself in the larger type:
- `0 ↦ 0`
- `1 ↦ 1`
- `2 ↦ 2`

The element `3 : Fin 4` is never hit.

## Your task

Prove that `Fin.castSucc` is not surjective. Recall that
`¬ Function.Surjective f` unfolds to
`Function.Surjective f → False`, which means: assume `f` is
surjective and derive a contradiction.

After `intro h`, the hypothesis `h` says that every element of
`Fin 4` has a preimage. Apply `h` to the missed element `3`:
use `obtain ⟨a, ha⟩ := h ⟨3, by omega⟩` to extract a supposed
preimage `a : Fin 3`.

Now `ha : Fin.castSucc a = ⟨3, _⟩`. Since `a : Fin 3`, its value
is at most `2`, so `Fin.castSucc a` has value at most `2`. But the
target has value `3` --- contradiction. Use `fin_cases a` to
enumerate the three possibilities and derive a contradiction in each.
"

/-- The canonical embedding `Fin 3 → Fin 4` is not surjective. -/
Statement : ¬ Function.Surjective (Fin.castSucc : Fin 3 → Fin 4) := by
  Hint "Start by assuming surjectivity for contradiction: `intro h`."
  intro h
  Hint "Now `h : Function.Surjective Fin.castSucc` says every element of `Fin 4`
  has a preimage. The element `3 : Fin 4` should be missed. Extract a preimage
  of `3` using `obtain ⟨a, ha⟩ := h ⟨3, by omega⟩`."
  obtain ⟨a, ha⟩ := h ⟨3, by omega⟩
  Hint "Now `a : Fin 3` and `ha : Fin.castSucc a = ⟨3, _⟩`. Since `a` can only
  be `0`, `1`, or `2`, and `Fin.castSucc` preserves values, none of these map to `3`.
  Use `fin_cases a` to check all three possibilities."
  Hint (hidden := true) "After `fin_cases a`, each case has `ha` as a false equation.
  Use `norm_num [Fin.ext_iff, Fin.val_castSucc] at ha` to derive the contradiction
  in each case. The full line:
  `fin_cases a <;> norm_num [Fin.ext_iff, Fin.val_castSucc] at ha`"
  fin_cases a <;> norm_num [Fin.ext_iff, Fin.val_castSucc] at ha

/-- `obtain ⟨a, ha⟩ := h` destructs a hypothesis `h : ∃ x, P x` into
a witness `a` and a proof `ha : P a`. It works like `rcases` for existential
hypotheses.

**Example**: If `h : ∃ a, f a = b`, then `obtain ⟨a, ha⟩ := h` gives
`a : α` and `ha : f a = b`.

**When to use**: When you have an existential hypothesis and need
the witness and the proof separately. -/
TacticDoc obtain

/-- `Fin.val_castSucc` states that `(Fin.castSucc i).val = i.val` for any
`i : Fin n`. The `castSucc` embedding preserves the underlying natural number value.

**When to use**: When you need to reason about the value of a `castSucc` element. -/
TheoremDoc Fin.val_castSucc as "Fin.val_castSucc" in "Fin"

NewTactic obtain
NewTheorem Fin.val_castSucc
TheoremTab "Fin"

DisabledTactic trivial decide native_decide simp aesop simp_all

Conclusion
"
The embedding `Fin.castSucc : Fin 3 → Fin 4` is not surjective because
the element `3 : Fin 4` has no preimage.

The proof by contradiction worked as follows:
1. Assume `h : Function.Surjective Fin.castSucc`
2. Apply `h` to `⟨3, _⟩ : Fin 4` to get a supposed preimage `a : Fin 3`
3. Check all three possibilities for `a`:
   - `a = 0`: `Fin.castSucc 0 = 0 ≠ 3` --- contradiction
   - `a = 1`: `Fin.castSucc 1 = 1 ≠ 3` --- contradiction
   - `a = 2`: `Fin.castSucc 2 = 2 ≠ 3` --- contradiction

**Proof move**: To disprove surjectivity, identify a missed element,
extract a preimage from the surjectivity hypothesis, and show every
possible preimage fails. The `obtain ⟨a, ha⟩ := h target` pattern
extracts the preimage, and `fin_cases a` checks every possibility.

**Counterexample thinking**: We showed one specific function is not
surjective. This gives a concrete instance of the general principle:
**a function from a smaller set to a larger set cannot be surjective**.

**What about the other direction?** In the next level, you will see
the dual failure: a function from `Fin 4` to `Fin 3` that is not
*injective*. Too many inputs, too few outputs --- two inputs must
collide.

**In plain language**: \"There is no surjection from $\\{0,1,2\\}$ onto
$\\{0,1,2,3\\}$. The inclusion $i \\mapsto i$ misses the element $3$:
checking each element of $\\{0,1,2\\}$, none maps to $3$.\"
"
