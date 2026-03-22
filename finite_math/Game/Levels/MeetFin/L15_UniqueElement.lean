import Game.Metadata

World "MeetFin"
Level 15

Title "The Unique Element"

Introduction "
# Fin 1 Has Exactly One Element

`Fin 1` is the type of natural numbers less than 1. The only such
number is 0, so `Fin 1` has **exactly one element**.

This means every `x : Fin 1` must equal `0`. To prove this, we'll
introduce a new tactic: **`ext`**.

The `ext` tactic is shorthand for `rw [Fin.ext_iff]` — it converts
a goal `a = b` (for `Fin` elements) into `a.val = b.val`. The name
stands for *extensionality*: two structured values are equal when
their components are equal.

`ext` is a **general-purpose tactic** — it works not just for `Fin`,
but for any type with an `@[ext]` attribute (functions, sets, and
many other types you'll meet later). Learning it here on `Fin` will
pay off when you encounter function extensionality in later worlds.

**Your task**: Prove that every element of `Fin 1` equals `0`.
Use `ext` then `omega`.
"

/-- `Fin 1` has exactly one element: `0`. -/
Statement (x : Fin 1) : x = 0 := by
  Hint "Use `ext` to convert the `Fin` equality to a value equality.
  This is the same as `rw [Fin.ext_iff]` but shorter."
  ext
  Hint "Now the goal is `x.val = 0`. Since `x : Fin 1`, you know
  `x.val < 1`, so `x.val = 0`. `omega` handles this."
  omega

Conclusion "
`Fin 1` is a **singleton type** — it has exactly one element, which
is `0`.

The `ext` tactic did the same work as `rw [Fin.ext_iff]`: it reduced
`Fin` equality to value equality. From now on, you can use either —
`ext` is shorter, `rw [Fin.ext_iff]` is more explicit.

This is the **Fin equality pattern** from Level 10: reduce to values,
then compute. Whether you write `ext; omega` or
`rw [Fin.ext_iff]; omega`, the effect is the same.

| `Fin n` | Number of elements | Character |
|---|---|---|
| `Fin 0` | 0 | Empty |
| `Fin 1` | 1 | Singleton |
| `Fin 2` | 2 | Coming soon! |
"

/-- `ext` proves equality of structured types by reducing to equality
of their components.

## Syntax
```
ext
```

## When to use it
When the goal is `a = b` where the type has an `@[ext]` attribute.

For `Fin n`: converts `a = b` to `a.val = b.val`.
For functions: converts `f = g` to `∀ x, f x = g x` (called `funext`).

## Example
```
-- Goal: x = 0  (where x : Fin 1)
ext
-- Goal: x.val = (0 : Fin 1).val
```

`ext` is a general-purpose tactic that works for many types beyond
`Fin`. It replaces `rw [Fin.ext_iff]` for Fin equality goals.
-/
TacticDoc ext

NewTactic ext

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Unique.eq_default Subsingleton.elim
