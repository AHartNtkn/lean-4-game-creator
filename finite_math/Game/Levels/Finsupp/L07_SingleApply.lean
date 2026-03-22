import Game.Metadata

World "Finsupp"
Level 7

Title "The Unified Evaluation Lemma"

Introduction "
# Behind the Scenes: `Finsupp.single_apply`

You have been using two separate lemmas to evaluate `Finsupp.single`:
- `single_eq_same` when the evaluation point matches the support point
- `single_eq_of_ne` when it does not

These are actually both special cases of a single unified lemma:

```
Finsupp.single_apply :
  Finsupp.single a b a' = if a = a' then b else 0
```

This is the *actual definition* of evaluation for `single`. It says:
look at whether the support point `a` equals the evaluation point `a'`.
If yes, return `b`. If no, return `0`.

The two lemmas you learned are just this definition with the `if`
resolved:
- When `a = a'`: the `if` returns `b` — that is `single_eq_same`
- When `a ≠ a'`: the `if` returns `0` — that is `single_eq_of_ne`

To resolve an `if` expression in a proof, use:
- `rw [if_pos h]` when `h` proves the condition is true
- `rw [if_neg h]` when `h` proves the condition is false

**Your task**: Evaluate `Finsupp.single 3 7` at position `5` by using
the unified lemma `single_apply` and then resolving the `if`.
"

/-- Evaluate using the unified `single_apply` lemma. -/
Statement : (Finsupp.single 3 7 : ℕ →₀ ℕ) 5 = 0 := by
  Hint "Start by rewriting with the unified evaluation lemma
  `Finsupp.single_apply`. This will expose the `if-then-else`."
  Hint (hidden := true) "Try `rw [Finsupp.single_apply]`. The goal
  becomes `(if 3 = 5 then 7 else 0) = 0`."
  rw [Finsupp.single_apply]
  Hint "The goal is now `(if 3 = 5 then 7 else 0) = 0`. Since
  `3 ≠ 5`, the condition is false. Create a proof with `have` and
  then use `if_neg` to resolve the `if`."
  Hint (hidden := true) "Try `have h : (3 : ℕ) ≠ 5 := by omega` then
  `rw [if_neg h]`. The type annotation `(3 : ℕ)` is needed
  because after `if_neg`, Lean sees the bare numeral `3` and
  needs to know its type to find the right `DecidableEq` instance."
  have h : (3 : ℕ) ≠ 5 := by omega
  rw [if_neg h]

Conclusion "
You have seen behind the curtain: the two evaluation lemmas
`single_eq_same` and `single_eq_of_ne` are both consequences of the
unified lemma `single_apply`, which uses an `if-then-else` to
decide between the two cases.

In practice, the specialized lemmas are more convenient — you do not
have to construct a proof of equality or inequality and then resolve
the `if`. That is why we taught them first and will continue using
them in the rest of this world. But knowing that `single_apply`
exists is important:

1. It is the canonical Mathlib form — if you search for evaluation
   of `Finsupp.single`, this is the lemma you will find.
2. It reveals the computational content: evaluation of a `single` is
   just an `if` check.
3. The tools `if_pos` and `if_neg` are general — they work for any
   `if` expression in Lean, not just Finsupp.

**Takeaway**: `single_eq_same` = `single_apply` + `if_pos rfl`.
`single_eq_of_ne` = `single_apply` + `if_neg h`.
"

/-- `if_pos` resolves a conditional expression when the condition is true:

`if_pos (h : P) : (if P then a else b) = a`

## Syntax
```
rw [if_pos h]     -- when h proves the condition
rw [if_pos rfl]   -- when the condition is an equality that holds by rfl
```

## When to use it
When the goal contains `if P then a else b` and you have a proof `h : P`.
-/
TheoremDoc if_pos as "if_pos" in "Logic"

/-- `if_neg` resolves a conditional expression when the condition is false:

`if_neg (h : ¬P) : (if P then a else b) = b`

## Syntax
```
rw [if_neg h]   -- when h proves ¬P (i.e., the condition is false)
```

## When to use it
When the goal contains `if P then a else b` and you have a proof
`h : ¬P`. Use `have h : ... := by omega` to manufacture `h` when
needed.
-/
TheoremDoc if_neg as "if_neg" in "Logic"

TheoremTab "Finsupp"
NewTheorem Finsupp.single_apply if_pos if_neg

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_eq_of_ne
