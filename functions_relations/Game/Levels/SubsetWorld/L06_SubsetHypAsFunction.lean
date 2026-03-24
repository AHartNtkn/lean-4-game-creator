import Game.Metadata

World "SubsetWorld"
Level 6

Title "Subset Hypotheses as Functions"

Introduction "
# Using a Subset Hypothesis

So far, you have been **proving** subset relations from scratch using
`intro x hx`. But what about **using** a subset hypothesis that you
already have?

If `h : s ⊆ t`, then `h` is essentially a **function**: give it a
proof that `x ∈ s`, and it returns a proof that `x ∈ t`. This is
because `s ⊆ t` unfolds to `∀ x, x ∈ s → x ∈ t`, which is exactly
the type of a function from membership proofs to membership proofs.

In this level, you have `h : s ⊆ t` and `hx : x ∈ s`. Your goal is
`x ∈ t`. Since `h` is a function that takes `x ∈ s` to `x ∈ t`,
you can close the goal with `exact h hx`.

Alternatively, you can use `apply h` to reduce the goal from `x ∈ t`
to `x ∈ s`, then close with `exact hx`.

**Proof plan**:
- `exact h hx` — apply `h` to `hx` directly
- OR: `apply h` then `exact hx` — reduce goal, then close
"

/-- If s ⊆ t and x ∈ s, then x ∈ t. -/
Statement (α : Type) (s t : Set α) (h : s ⊆ t) (x : α) (hx : x ∈ s) :
    x ∈ t := by
  Hint "The goal is `x ∈ t`. You have `h : s ⊆ t` (a function from
  `x ∈ s` to `x ∈ t`) and `hx : x ∈ s`. Apply `h` to `hx`:
  use `exact h hx`."
  Hint (hidden := true) "`exact h hx` applies the subset hypothesis `h`
  to the membership proof `hx`, producing a proof of `x ∈ t`.

  Alternatively: `apply h` reduces the goal to `x ∈ s`, then `exact hx`."
  Branch
    apply h
    Hint "The goal is now `x ∈ s`. You have `hx : x ∈ s`.
    Use `exact hx`."
    exact hx
  exact h hx

Conclusion "
You just used a subset hypothesis as a function for the first time!

The key insight: `h : s ⊆ t` is not just a statement — it is a
**function** that converts membership proofs. Given `hx : x ∈ s`,
the expression `h hx` is a proof of `x ∈ t`.

| Expression | Type | Meaning |
|---|---|---|
| `h` | `s ⊆ t` | \"every element of s is in t\" |
| `hx` | `x ∈ s` | \"x is in s\" |
| `h hx` | `x ∈ t` | \"therefore x is in t\" |

**Under the hood**: `s ⊆ t` has the type `∀ x, x ∈ s → x ∈ t` —
which IS a function type. When you write `h hx`, you are doing
ordinary function application: feeding a membership proof to a
function that converts membership proofs. This is not a special rule
for subsets — it is the same Curry-Howard correspondence you saw in
Set World, where membership itself is function application.

This pattern — applying a subset hypothesis to a membership proof —
is the fundamental way to *use* subset facts. You will chain multiple
such applications in the next levels.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
