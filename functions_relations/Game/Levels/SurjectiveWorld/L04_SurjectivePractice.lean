import Game.Metadata

World "SurjectiveWorld"
Level 4

Title "Surjective but Not Injective"

TheoremTab "Function"

Introduction "
# A Different Kind of Witness

Now prove that `n ↦ n / 2` on ℕ is surjective.

This function is very different from Level 1's `n ↦ n + 1`:
- The domain is ℕ, not ℤ
- The witness is `2 * b` (multiplication, not subtraction)
- The function is surjective but NOT injective (e.g., `3 / 2 = 1 = 2 / 2`)

**Finding the witness**: You need `a` with `a / 2 = b`. Since `(2 * b) / 2 = b`
for any natural number `b`, the witness is `2 * b`.

This is another instance of the **construct-and-verify** proof strategy:
1. Solve the equation `f a = b` algebraically to find the witness `a`
2. Provide the witness with `use`
3. Verify with `omega`

You used this same strategy in Level 1 — the function and witness change,
but the proof skeleton stays the same.
"

/-- The halving function n ↦ n / 2 on ℕ is surjective. -/
Statement : Function.Surjective (fun n : ℕ => n / 2) := by
  Hint "Start with `intro b` as always for a surjectivity proof."
  intro b
  Hint "You need `a : ℕ` with `a / 2 = b`. The witness is `2 * b`, since
  `(2 * b) / 2 = b`. Use `use 2 * b`."
  Hint (hidden := true) "`use 2 * b` then `show 2 * b / 2 = b` then `omega`."
  use 2 * b
  Hint "The goal is `(fun n => n / 2) (2 * b) = b`, which is definitionally
  `2 * b / 2 = b`. You can use `show 2 * b / 2 = b` to make the arithmetic
  explicit, then `omega` to close it. (Note: `omega` may also work directly
  here without the `show` step.)"
  show 2 * b / 2 = b
  Hint "The goal is now `2 * b / 2 = b`. Use `omega`."
  omega

Conclusion "
Same construct-and-verify strategy, but a very different function:

| Level 1: `n ↦ n + 1` on ℤ | Level 4: `n ↦ n / 2` on ℕ |
|---|---|
| Witness: `b - 1` (subtraction) | Witness: `2 * b` (multiplication) |
| Injective AND surjective | Surjective but NOT injective |

**The construct-and-verify strategy**: Every surjectivity proof for an
arithmetic function follows the same pattern:
1. Solve `f a = b` for `a` to find the witness
2. `use` the witness
3. Verify with `omega`

The function changes, the witness changes, but the *strategy* is the same.
You will see this pattern repeatedly — recognizing it is the key to
efficient surjectivity proofs.

**Fibers — the unifying framework**: The set `f ⁻¹' {b}` is called the
**fiber** of `f` over `b`. Fibers give a clean way to see injective,
surjective, and bijective as a single family:

| Property | Fiber condition | Meaning |
|---|---|---|
| Injective | Every fiber has **at most 1** element | No collisions |
| Surjective | Every fiber has **at least 1** element | No gaps |
| Bijective | Every fiber has **exactly 1** element | Perfect pairing |

Injectivity and surjectivity control **different aspects** of fiber size.
That is WHY they are independent — a function can have large fibers
(not injective) while still covering every output (surjective), or hit
each output at most once (injective) while missing some outputs entirely
(not surjective).

**The four cases — injective and surjective are independent**:

| | Injective | Not injective |
|---|---|---|
| **Surjective** | `n ↦ n + 1` on ℤ (Level 1) | `n ↦ n / 2` on ℕ (this level) |
| **Not surjective** | `n ↦ 2 * n` on ℕ (Level 2) | e.g., constant function |

A function can be one, both, or neither. These are genuinely independent
properties.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl
