import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 3

Title "Distinct pairs in Fin 3 x Fin 3"

Introduction
"
# Building Pairs from `Fin 3`

Given two finite types, you can form their **product**. An element of
`Fin 3 × Fin 3` is a pair `(a, b)` where both `a` and `b` are elements
of `Fin 3`.

Since `Fin 3` has 3 elements, the product `Fin 3 × Fin 3` has
`3 × 3 = 9` elements. This is the **multiplication principle** for
finite types.

## Your task

Construct a pair in `Fin 3 × Fin 3` whose components are *distinct*:
the first component is not equal to the second.

Formally, find `p : Fin 3 × Fin 3` such that `p.1 ≠ p.2`.

Use `refine ⟨(0, 1), ?_⟩` to provide the pair `(0, 1)` and leave
the inequality goal. Then prove `(0 : Fin 3) ≠ (1 : Fin 3)` by
assuming they are equal (`intro h`), extracting the value-level
consequence (`have hv := congr_arg Fin.val h`), and closing the
arithmetic contradiction with `norm_num at hv`.
"

/-- There exists a pair in `Fin 3 × Fin 3` with distinct components. -/
Statement : ∃ p : Fin 3 × Fin 3, p.1 ≠ p.2 := by
  Hint "Provide a witness pair with distinct components.
  Try `refine ⟨(0, 1), ?_⟩`."
  refine ⟨(0, 1), ?_⟩
  Hint "Now prove `(0 : Fin 3) ≠ (1 : Fin 3)`. Remember that `≠` means
  \"not equal\", which unfolds to `(0 : Fin 3) = (1 : Fin 3) → False`.
  Use `intro h` to assume they are equal."
  intro h
  Hint "The hypothesis `h : (0 : Fin 3) = (1 : Fin 3)` implies their underlying
  natural number values are equal. Extract this with `have hv := congr_arg Fin.val h`.
  Then `norm_num at hv` derives the contradiction `0 = 1 → False`."
  Hint (hidden := true) "After `have hv := congr_arg Fin.val h`, the hypothesis `hv`
  says `0 = 1` at the natural number level. Try `norm_num at hv` to finish."
  have hv := congr_arg Fin.val h
  norm_num at hv

/-- `refine e` provides a partial proof term `e` that may contain placeholders `?_`.
Each placeholder becomes a new goal. This lets you supply part of a term and leave
the rest for later.

**Example**: If the goal is `∃ x, P x`, then `refine ⟨42, ?_⟩` provides the witness
`42` and leaves `P 42` as the remaining goal.

**When to use**: When you know part of the answer (e.g., a witness) but still need
to prove a property of it. -/
TacticDoc refine

NewTactic refine

DisabledTactic trivial decide native_decide simp aesop simp_all

Conclusion
"
You constructed the pair `(0, 1)` in `Fin 3 × Fin 3` and proved its
components are distinct by deriving a contradiction: if `0 = 1` as
elements of `Fin 3`, then their underlying values `0` and `1` would be
equal as natural numbers, which is impossible.

The full product `Fin 3 × Fin 3` has 9 elements:
```
(0,0) (0,1) (0,2)
(1,0) (1,1) (1,2)
(2,0) (2,1) (2,2)
```

Of these, 6 have distinct components (the off-diagonal entries).

**Proof move**: The pattern `intro h; have hv := congr_arg Fin.val h; norm_num at hv`
for disproving equalities between distinct `Fin` elements is worth remembering.
It extracts the value-level equality and lets `norm_num` find the contradiction.

**In plain language**: \"The pair $(0, 1)$ has distinct components because
$0 \\neq 1$.\"
"
