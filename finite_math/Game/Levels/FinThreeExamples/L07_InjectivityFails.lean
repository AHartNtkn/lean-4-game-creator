import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 7

Title "Injectivity fails: Fin 4 to Fin 3"

Introduction
"
# A Specific Function from `Fin 4` to `Fin 3` Is Not Injective

In the previous level, you saw that a function from `Fin 3` to `Fin 4`
cannot be surjective (not enough inputs to cover all outputs). The dual
statement is: a function from `Fin 4` to `Fin 3` cannot be injective
(too many inputs for too few outputs --- two inputs must collide).

This is the other face of the **pigeonhole principle**: if you put 4
pigeons into 3 holes, at least two pigeons share a hole.

## The function

Consider the function `f : Fin 4 → Fin 3` defined by:
- `f 0 = 0`
- `f 1 = 1`
- `f 2 = 2`
- `f 3 = 0`

Notice that `f 0 = f 3 = 0`, but `0 ≠ 3` in `Fin 4`. So `f` is not
injective.

## Your task

Prove `¬ Function.Injective f`. After `intro h` (assuming injectivity
for contradiction), apply `h` to the collision: since `f 0 = f 3`
(both equal `0 : Fin 3`), injectivity would force `0 = 3` in `Fin 4`.

Write `have h03 : (0 : Fin 4) = (3 : Fin 4) := h rfl`. Here `rfl`
proves `f 0 = f 3` because the function sends both to `0`.

Then derive a contradiction from `h03`: use
`have := congr_arg Fin.val h03` to get `0 = 3` at the natural number
level, and `norm_num at this` to close.
"

/-- A specific function from `Fin 4` to `Fin 3` is not injective. -/
Statement : ¬ Function.Injective
    (fun i : Fin 4 => match i with
      | 0 => (0 : Fin 3) | 1 => 1 | 2 => 2 | 3 => 0) := by
  Hint "Start by assuming injectivity for contradiction: `intro h`."
  intro h
  Hint "Now `h` says the function is injective. We need to find two distinct
  inputs that map to the same output. The inputs `0` and `3` both map to
  `0 : Fin 3`. Apply injectivity to this collision:
  `have h03 : (0 : Fin 4) = (3 : Fin 4) := h rfl`."
  Hint (hidden := true) "Here `rfl` proves `f 0 = f 3` because the match
  expression evaluates both to `(0 : Fin 3)`. After `h rfl`, you get
  `(0 : Fin 4) = (3 : Fin 4)`, which is false."
  have h03 : (0 : Fin 4) = (3 : Fin 4) := h rfl
  Hint "Now `h03 : (0 : Fin 4) = (3 : Fin 4)`. Extract the value-level
  equation with `have := congr_arg Fin.val h03`, then close with
  `norm_num at this`."
  have := congr_arg Fin.val h03
  norm_num at this

DisabledTactic trivial decide native_decide simp aesop simp_all

Conclusion
"
The function `0 ↦ 0, 1 ↦ 1, 2 ↦ 2, 3 ↦ 0` from `Fin 4` to `Fin 3`
is not injective because `f(0) = f(3) = 0`, yet `0 ≠ 3` in `Fin 4`.

The proof by contradiction:
1. Assume `h : Function.Injective f`
2. Since `f 0 = f 3` (both equal `0`), apply `h` to get `0 = 3` in `Fin 4`
3. But `0 ≠ 3` --- contradiction!

**Dual of the surjectivity failure**: In Level 6, you showed that
`Fin 3 → Fin 4` cannot be surjective (not enough inputs). Here you
showed that `Fin 4 → Fin 3` cannot be injective (too many inputs).
These are two faces of the same coin --- the pigeonhole principle.

**Proof move**: To disprove injectivity, find a *specific collision*:
two distinct inputs with the same output. Apply injectivity with `h rfl`
(where `rfl` witnesses `f a = f b`), then derive a contradiction from
the resulting false equality.

**In plain language**: \"The function $f$ with $f(0) = f(3) = 0$, $f(1) = 1$,
$f(2) = 2$ sends both $0$ and $3$ to $0$. Since $f(0) = f(3)$ but
$0 \\neq 3$, the function is not injective.\"
"
