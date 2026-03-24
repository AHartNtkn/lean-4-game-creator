import Game.Metadata

World "SurjectiveWorld"
Level 2

Title "A Non-Surjective Function"

TheoremTab "Function"

Introduction "
# Disproving Surjectivity

Not every function is surjective. The doubling function `n ↦ 2 * n` on ℕ
only hits even numbers — the odd number `1` has no preimage:

There is no `a : ℕ` with `2 * a = 1`.

(Compare with Injective World: `n ↦ 2 * n` IS injective but is NOT
surjective. Conversely, `n ↦ n / 2` is NOT injective but IS surjective
on ℕ. Injectivity and surjectivity are independent properties.)

**The proof shape for ¬ Surjective f**:

Since `¬ P` means `P → False`, start with `intro h` to assume surjectivity,
then derive a contradiction.

For `¬ Surjective (fun n : ℕ => 2 * n)`:
1. `intro h` — assume `h : Surjective (fun n => 2 * n)`
2. Apply `h` to `1` to get a witness `a` with `2 * a = 1`
3. Extract the witness with `obtain`
4. Derive a contradiction (no natural number satisfies `2 * a = 1`)

**Recall `obtain`** (from Set World): To extract the witness from an
existential hypothesis `h : ∃ x, P x`, use:

```
obtain ⟨x, hx⟩ := h
```

This gives you `x : α` and `hx : P x` in your context.
Type ⟨ as `\\<` and ⟩ as `\\>` in the editor.
"

/-- The doubling function n ↦ 2 * n is not surjective on ℕ. -/
Statement : ¬ Function.Surjective (fun n : ℕ => 2 * n) := by
  Hint "Since `¬ P` means `P → False`, start with `intro h` to assume
  surjectivity and aim for a contradiction."
  intro h
  Hint "Now `h : Function.Surjective (fun n => 2 * n)` says that for
  every `b : ℕ`, there exists `a` with `2 * a = b`. Apply `h` to `1`
  and extract the witness:

  `obtain ⟨a, ha⟩ := h 1`

  (Type ⟨ as `\\<` and ⟩ as `\\>`.)"
  Hint (hidden := true) "`obtain ⟨a, ha⟩ := h 1`"
  obtain ⟨a, ha⟩ := h 1
  Hint "You have `ha : 2 * a = 1` (possibly displayed with a lambda
  wrapper). But there is no natural number `a` satisfying `2 * a = 1`:
  if `a = 0` then `2 * 0 = 0`, and if `a ≥ 1` then `2 * a ≥ 2`.

  Create the explicit equation if needed:
  `have ha' : 2 * a = 1 := ha`
  then use `omega` to derive the contradiction."
  Hint (hidden := true) "`have ha' : 2 * a = 1 := ha` then `omega`.
  (Note: `omega` may also work directly without the `have` step.)"
  Branch
    change 2 * a = 1 at ha
    Hint "The goal is `False` and you have `ha : 2 * a = 1`. No natural
    number satisfies this — `omega` can close the goal."
    omega
  have ha' : 2 * a = 1 := ha
  omega

Conclusion "
You disproved surjectivity by finding a missing output!

**Two proof shapes side by side**:

| Proving `Surjective f` | Proving `¬ Surjective f` |
|---|---|
| `intro b` | `intro h` |
| `use witness` + verify | `obtain ⟨a, ha⟩ := h b` + contradict |
| Construct a preimage | Exhibit an unreachable output |

**Recall `obtain`**: `obtain ⟨x, hx⟩ := h` destructures an
existential hypothesis `h : ∃ x, P x` into a witness `x` and a proof
`hx : P x`. You used this in Set World — here you will use `obtain`
extensively whenever you need to extract a witness from a surjectivity
hypothesis.

**Why `omega` closes `False`**: The hypothesis `2 * a = 1` with `a : ℕ`
is impossible: `2 * a` is always even, but `1` is odd. `omega` detects
this and closes the `False` goal.

**Injective vs. Surjective — the asymmetry**: The doubling function
`n ↦ 2 * n` is injective (from Injective World) but not surjective.
The halving function `n ↦ n / 2` is surjective but not injective
(from Injective World Level 3). These properties are **independent** —
a function can be one, both, or neither.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl
