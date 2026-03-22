import Game.Metadata

World "MeetFin"
Level 5

Title "When Are Fin Elements Equal?"

Introduction "
# Fin Extensionality

When are two elements of `Fin n` equal? Exactly when their underlying
natural number values are equal.

This is stated by `Fin.ext_iff`:

$$i = j \\iff i.\\text{val} = j.\\text{val}$$

You can use `rw [Fin.ext_iff]` to convert a goal about `Fin` equality
into a goal about natural number equality. This is one of the most
important moves in `Fin` reasoning.

**Your task**: Given two elements `i j : Fin 5` with `h : i.val = j.val`,
prove that `i = j`.
"

/-- Two `Fin 5` elements with the same value are equal. -/
Statement (i j : Fin 5) (h : i.val = j.val) : i = j := by
  Hint "The goal is `i = j` where `i j : Fin 5`. Use `rw [Fin.ext_iff]`
  to convert this to `i.val = j.val`."
  rw [Fin.ext_iff]
  Hint "Now the goal is `i.val = j.val`, which is exactly `{h}`."
  exact h

Conclusion "
The pattern `rw [Fin.ext_iff]` converts `Fin` equality to value equality.
You'll use this pattern repeatedly — whenever you need to prove two `Fin`
elements are equal, reduce it to their values.

The converse direction is trivial: if `i = j` then certainly
`i.val = j.val` (applying a function preserves equality). You'll
practice this direction in the next level.

In plain mathematics, this is the obvious fact that elements of
$\\{0, \\ldots, n-1\\}$ are just numbers, and two numbers are equal
when they're the same number. So why does Lean need a lemma for this?

Because `Fin n` is a **subtype** — a wrapper around a natural number
and a proof. An element `i : Fin n` is really `⟨i.val, i.isLt⟩`:
a number *packaged with* a proof that it's in range. Lean's type
system distinguishes between the *wrapper* `i` and the *contained
value* `i.val`. Two wrappers could in principle differ (maybe the
proofs are different?) even if the values match. `Fin.ext_iff` says:
no, the proof component doesn't matter — equality of the wrapper
is determined entirely by equality of the contained value. (You'll
see why the proof doesn't matter when you learn about *proof
irrelevance* in Level 11.)

*Shortcut*: the `ext` tactic does the same thing as `rw [Fin.ext_iff]`
— it converts `i = j` to `i.val = j.val` directly. You'll see `ext`
used for other types later (like function extensionality). We'll stick
with `rw [Fin.ext_iff]` for now since it makes the step explicit.
"

/-- `Fin.ext_iff` states that two elements of `Fin n` are equal if and
only if their underlying values are equal:

`a = b ↔ a.val = b.val`

## Syntax
```
rw [Fin.ext_iff]
```
Converts a goal `a = b` (for `a b : Fin n`) to `a.val = b.val`.

```
rw [Fin.ext_iff] at h
```
Converts a hypothesis `h : a = b` to `h : a.val = b.val`.

## When to use it
Whenever you need to prove or decompose equality of `Fin` elements.

## Example
```
-- Goal: i = j  (where i j : Fin 5)
rw [Fin.ext_iff]
-- Goal: i.val = j.val
```
-/
TheoremDoc Fin.ext_iff as "Fin.ext_iff" in "Fin"

TheoremTab "Fin"
NewTheorem Fin.ext_iff

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
