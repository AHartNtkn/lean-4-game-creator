import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 2

Title "Evaluating a function on Fin 3"

Introduction
"
# Computing with a Function on `Fin 3`

A function on a finite type is completely determined by its values
on each element. For `Fin 3`, a function `f : Fin 3 → Nat` is just
a lookup table with three entries: `f 0`, `f 1`, and `f 2`.

## Your task

Consider the function `f : Fin 3 → Nat` defined by `f i = 2 * i.val + 1`.
This maps:
- `0 ↦ 1`
- `1 ↦ 3`
- `2 ↦ 5`

Prove that `f` maps every element to an odd number. Formally, prove
that for every `i : Fin 3`, the value `(2 * i.val + 1) % 2 = 1`.

Use `intro i`, then `fin_cases i` to split into three cases.
In each case, you need to verify a concrete arithmetic fact.
Use `norm_num` to close each case.

We have disabled `decide` so that you practice the `fin_cases` +
per-case verification pattern. This is the manual proof move ---
later worlds may let you automate it, but here you should see each
case explicitly.
"

/-- Every element of `Fin 3` is mapped to an odd number by `2 * i + 1`. -/
Statement : ∀ i : Fin 3, (2 * i.val + 1) % 2 = 1 := by
  Hint "Start with `intro i` to pick an arbitrary element."
  intro i
  Hint "Use `fin_cases i` to split into the three cases for `Fin 3`."
  fin_cases i
  · Hint "The goal is `(2 * 0 + 1) % 2 = 1`. Use `norm_num` to evaluate."
    norm_num
  · Hint "The goal is `(2 * 1 + 1) % 2 = 1`. Use `norm_num` to evaluate."
    norm_num
  · Hint "The goal is `(2 * 2 + 1) % 2 = 1`. Use `norm_num` to evaluate."
    norm_num

DisabledTactic trivial decide native_decide omega simp aesop simp_all

Conclusion
"
By checking each element:
- `i = 0`: `(2 * 0 + 1) % 2 = 1 % 2 = 1` ✓
- `i = 1`: `(2 * 1 + 1) % 2 = 3 % 2 = 1` ✓
- `i = 2`: `(2 * 2 + 1) % 2 = 5 % 2 = 1` ✓

Every value is odd.

**Proof shape**: `intro` → `fin_cases` → per-case `norm_num`. This is
the core pattern for verifying a property of a function on a small
finite type. Each case reduces to a concrete numeric check.

Notice that we did NOT use `decide` here. While `decide` could verify
this automatically, the `fin_cases` approach makes each case visible.
You can see exactly what the function does on each input --- that
visibility is the point of an example world.

**In plain language**: \"For each $i \\in \\{0, 1, 2\\}$, the number
$2i + 1$ is odd. We check: $1$, $3$, $5$ --- all odd.\"
"
