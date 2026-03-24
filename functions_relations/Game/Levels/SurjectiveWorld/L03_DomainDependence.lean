import Game.Metadata

World "SurjectiveWorld"
Level 3

Title "Domain Matters: n + 1 on ℕ"

TheoremTab "Function"

Introduction "
# The Same Formula, a Different Domain

In Level 1, you proved that `n ↦ n + 1` is surjective on ℤ. The witness
for any `b : ℤ` was `b - 1`, because `(b - 1) + 1 = b`.

But the **same formula** on ℕ is NOT surjective! The problem: `0` has
no preimage. There is no `a : ℕ` with `a + 1 = 0`, because natural
numbers cannot be negative.

**The lesson**: Surjectivity depends on the **domain and codomain**, not
just the formula. The expression `n + 1` defines a surjective function
on ℤ (which has negative numbers for witnesses) but a non-surjective
function on ℕ (which does not).

**Proof strategy**: Use the same shape as Level 2:
1. `intro h` to assume surjectivity
2. Apply `h` to the problematic element (`0`)
3. Extract the witness and derive a contradiction
"

/-- The successor function n ↦ n + 1 is NOT surjective on ℕ. -/
Statement : ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  Hint "Since `¬ P` means `P → False`, start with `intro h` to assume
  surjectivity and aim for a contradiction."
  intro h
  Hint "Now `h : Function.Surjective (fun n => n + 1)` says every
  `b : ℕ` has a preimage under `n + 1`. But `0` has no preimage:
  `a + 1 ≥ 1` for all `a : ℕ`.

  Apply `h` to `0` and extract the witness:
  `obtain ⟨a, ha⟩ := h 0`"
  Hint (hidden := true) "`obtain ⟨a, ha⟩ := h 0`."
  obtain ⟨a, ha⟩ := h 0
  Hint "You have `ha : a + 1 = 0` (possibly displayed with a lambda
  wrapper). But no natural number satisfies `a + 1 = 0`.

  Create the explicit equation if needed:
  `have ha' : a + 1 = 0 := ha`
  then use `omega` to derive the contradiction."
  Hint (hidden := true) "`have ha' : a + 1 = 0 := ha` then `omega`.
  (Note: `omega` may also work directly without the `have` step.)"
  Branch
    change a + 1 = 0 at ha
    Hint "The goal is `False` and you have `ha : a + 1 = 0`. No natural
    number satisfies this — `omega` can close the goal."
    omega
  have ha' : a + 1 = 0 := ha
  omega

Conclusion "
The same formula, different domains, different results:

| Domain | `n ↦ n + 1` | Why |
|---|---|---|
| ℤ (Level 1) | Surjective | Witness `b - 1` exists for all `b` |
| ℕ (this level) | NOT surjective | `0` has no preimage (`a + 1 ≥ 1`) |

**The domain matters**: Surjectivity is a property of the function AS A
MAP between specific sets, not just of the formula. Changing the domain
from ℤ to ℕ removed the witness for `0`, breaking surjectivity.

**Three proof shapes so far**:

| Goal | Shape | Key step |
|---|---|---|
| `Surjective f` (L1) | `intro b; use witness; omega` | Find the witness |
| `¬ Surjective f` (L2) | `intro h; obtain from h b; omega` | Find the missing output |
| `¬ Surjective f` (this) | `intro h; obtain from h 0; omega` | Same shape, different `b` |
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl
