import Game.Metadata

World "FinsetImage"
Level 15

Title "Injective Functions Preserve Size"

Introduction "
# When Does Image Preserve Cardinality?

Level 12 showed that $|f(S)| \\leq |S|$ always. When does equality hold?

A function $f$ is **injective** (one-to-one) if different inputs
always produce different outputs:

$$f(a) = f(b) \\implies a = b$$

In Lean, this is `Function.Injective f`:
```
Function.Injective f  means  ∀ a b, f a = f b → a = b
```

When `f` is injective, no two elements of `s` can collide in the
image, so the image has exactly as many elements as `s`:

$$f \\text{ injective} \\implies |f(S)| = |S|$$

In Lean: `Finset.card_image_of_injective s hf : (s.image f).card = s.card`

**Your task**: Given that `f` is injective and `a ∈ s`, prove two things:
1. `f a ∈ s.image f` (the forward membership move from Levels 1-2)
2. `(s.image f).card = s.card` (applying `card_image_of_injective`)
"

/-- Injective functions preserve both membership and cardinality. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (hf : Function.Injective f)
    (a : ℕ) (ha : a ∈ s) :
    f a ∈ s.image f ∧ (s.image f).card = s.card := by
  Hint "Use `constructor` to split into the membership part and the
  cardinality part."
  constructor
  -- Part 1: f a ∈ s.image f
  · Hint "Prove `f a ∈ s.image f` using the witness pattern from
    Levels 1-2. The witness is `a` itself.
    Use `rw [Finset.mem_image]` to convert to an existential."
    rw [Finset.mem_image]
    Hint "The witness for `f a` in the image is `a` itself:
    `a ∈ s` (given by `ha`) and `f a = f a` (by `rfl`).
    Try `exact ⟨a, ha, rfl⟩`."
    exact ⟨a, ha, rfl⟩
  -- Part 2: (s.image f).card = s.card
  · Hint "Apply `Finset.card_image_of_injective`.
    Try `exact Finset.card_image_of_injective s hf`."
    exact Finset.card_image_of_injective s hf

Conclusion "
Two key results:
1. **Membership**: If `a ∈ s`, then `f a ∈ s.image f` — the witness
   is `a` itself, with equation `f a = f a` (which is `rfl`).
2. **Cardinality**: If `f` is injective, then `(s.image f).card = s.card`.

`Finset.card_image_of_injective` is the positive counterpart to
`Finset.card_image_le`:
- `card_image_le`: $|f(S)| \\leq |S|$ (always)
- `card_image_of_injective`: $|f(S)| = |S|$ (when $f$ is injective)

But where does the injectivity hypothesis `hf` come from? In this
level it was given. In the next level, you'll learn how to **prove**
that a function is injective.
"

/-- `Function.Injective f` means that `f` maps distinct inputs to
distinct outputs: `∀ a b, f a = f b → a = b`.

## Definition
```
Function.Injective f  :=  ∀ a b, f a = f b → a = b
```

## How to prove it
```
intro a b h  -- introduces a, b, and h : f a = f b
-- goal: a = b
-- use algebra or omega to derive a = b from f a = f b
```

## When to use it
When you need to show that a function preserves cardinality
(via `Finset.card_image_of_injective`), or that distinct inputs
give distinct outputs.
-/
DefinitionDoc Function.Injective as "Function.Injective"

/-- `Finset.card_image_of_injective s hf` states that
`(s.image f).card = s.card` when `hf : Function.Injective f`.

## Syntax
```
exact Finset.card_image_of_injective s hf
```

## When to use it
When you need to show that an image preserves the cardinality of
a finset. Requires a proof that the function is injective.
-/
TheoremDoc Finset.card_image_of_injective as "Finset.card_image_of_injective" in "Finset"

NewDefinition Function.Injective
NewTheorem Finset.card_image_of_injective

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
