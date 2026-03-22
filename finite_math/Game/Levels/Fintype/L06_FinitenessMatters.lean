import Game.Metadata

World "Fintype"
Level 6

Title "Finiteness Matters"

Introduction "
# Why Finiteness Matters

You've now learned all five composition rules:

| Construction | Formula | Lemma |
|---|---|---|
| `Fin n` | `n` | `card_fin` |
| `Bool` | `2` | `card_bool` |
| `α × β` | `card α * card β` | `card_prod` |
| `α ⊕ β` | `card α + card β` | `card_sum` |
| `α → β` | `card β ^ card α` | `card_fun` |

But there's a catch: these rules only work for **finite types** — types
with a `[Fintype α]` instance.

Consider the natural numbers `ℕ`. There are infinitely many functions
`ℕ → Bool` (for each natural number, independently choose `true` or
`false`). The \"formula\" `2 ^ card ℕ` is meaningless because `card ℕ`
is undefined — `ℕ` has no `Fintype` instance. Writing `Fintype.card ℕ`
in Lean is a type error.

The `[Fintype α]` constraint in the statement below is what makes the
counting valid. Without it, `Fintype.card α` would be a type error.

**Your task**: Prove that for any finite type `α`, the number of
functions from `α` to `Bool` is `2 ^ Fintype.card α`. This combines
`card_fun` and `card_bool`.
"

/-- The number of functions from a finite type to Bool is 2^(card α). -/
Statement (α : Type*) [DecidableEq α] [Fintype α] :
    Fintype.card (α → Bool) = 2 ^ Fintype.card α := by
  Hint "Use `rw [Fintype.card_fun]` to decompose the function type,
  then evaluate `Fintype.card Bool` with `card_bool`."
  Hint (hidden := true) "Try `rw [Fintype.card_fun, Fintype.card_bool]`."
  rw [Fintype.card_fun, Fintype.card_bool]

Conclusion "
Every finite type `α` has exactly `2 ^ (card α)` functions to `Bool` —
one for each subset of `α`. (This is the type-theoretic version of the
fact that a set with `n` elements has `2^n` subsets.)

The key takeaway: the `[Fintype α]` typeclass constraint isn't
decoration — it's what makes counting possible. If you tried to state
this for `ℕ`, Lean would refuse: there is no `Fintype ℕ` instance.

In general, whenever you see `[Fintype α]` in a statement, it means
the result only holds for finite types. This is Lean enforcing a
mathematical precondition at the type level.

Next: practice mixing composition rules on concrete types.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
