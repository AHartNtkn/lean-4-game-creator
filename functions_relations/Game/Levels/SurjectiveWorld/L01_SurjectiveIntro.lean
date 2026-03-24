import Game.Metadata

World "SurjectiveWorld"
Level 1

Title "The Surjectivity Proof Shape"

TheoremTab "Function"

Introduction "
# Surjective Functions

A function `f` is **surjective** (onto) if every element of the codomain
is hit by `f`. In Lean:

$$\\text{Surjective}(f) \\;\\;:\\equiv\\;\\; \\forall\\, b,\\;\\; \\exists\\, a,\\;\\; f(a) = b$$

This is the dual of injectivity. An injective function never collapses
two inputs to the same output; a surjective function never misses any
output.

**The canonical proof shape**: To prove `Surjective f`, you always start
the same way:

```
intro b
```

This gives you `b : β` (an arbitrary element of the codomain). Your job
is to find a witness `a` such that `f a = b`, using:

```
use witness
```

Then verify that the witness works (often with `omega` or `rfl`).

**Your task**: Prove that `n ↦ n + 1` on ℤ is surjective.

The witness for any `b : ℤ` is `b - 1`, because `(b - 1) + 1 = b`.
"

/-- `Function.Surjective f`, written `Function.Surjective f`, means
that every element of the codomain is in the range of `f`:

$$\\forall\\, b,\\;\\; \\exists\\, a,\\;\\; f(a) = b$$

## Syntax
```
hsurj : Function.Surjective f
hsurj b : ∃ a, f a = b     -- apply to a specific element
```

## When to use it
When you need a preimage of a specific element. Apply the surjectivity
hypothesis to any element of the codomain to get an existential witness.

## Example
```
-- hsurj : Function.Surjective f, b : β
obtain ⟨a, ha⟩ := hsurj b    -- a : α, ha : f a = b
```

## Warning
Surjectivity is about the FUNCTION, not a specific element. You need
a hypothesis `Function.Surjective f` in scope.
-/
DefinitionDoc Function.Surjective as "Function.Surjective"

/-- The function n ↦ n + 1 on ℤ is surjective. -/
Statement : Function.Surjective (fun n : ℤ => n + 1) := by
  Hint "Start with `intro b` to get an arbitrary element of the codomain."
  intro b
  Hint "The goal is `∃ a, (fun n => n + 1) a = b`, i.e., find `a` with
  `a + 1 = b`. The witness is `b - 1`. Use `use b - 1`."
  Hint (hidden := true) "`use b - 1` then `show b - 1 + 1 = b` then `omega`."
  use b - 1
  Hint "The goal is `(fun n => n + 1) (b - 1) = b`, which is definitionally
  `b - 1 + 1 = b`. You can use `show b - 1 + 1 = b` to make the arithmetic
  explicit, then `omega` to close it. (Note: `omega` may also work directly
  here without the `show` step.)"
  show b - 1 + 1 = b
  Hint "The goal is now `b - 1 + 1 = b`. This is linear arithmetic
  on ℤ — use `omega`."
  omega

Conclusion "
You proved your first surjectivity! The canonical proof shape is:

```
intro b           -- take an arbitrary output
use witness       -- provide a preimage
omega             -- verify the witness works
```

**Compare with injectivity**:

| Injective | Surjective |
|---|---|
| `intro a b hab` | `intro b` |
| Show `a = b` from `f a = f b` | Find `a` with `f a = b` |
| Preserves distinctness | Covers the codomain |

**The construct-and-verify strategy**: Finding the right witness is the
key challenge. For `n ↦ n + 1`, you solved `a + 1 = b` for `a` to get
`b - 1`, then verified with `omega`. This three-step strategy —
(1) solve the equation to find the witness, (2) `use` it, (3) verify —
is the canonical approach for arithmetic surjectivity proofs. You will
use it again in Level 4.

**Recall**: You already know `use` from earlier worlds. The new idea
here is that surjectivity proofs always follow the `intro b; use witness`
pattern.
"

NewDefinition Function.Surjective

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp Function.RightInverse.surjective Function.HasRightInverse.surjective
