import Game.Metadata

World "MeetFin"
Level 21

Title "Proving Inequality"

Introduction "
# Proving Two Fin Elements Are Not Equal

In Level 17, you used `absurd` when a bound was violated — the value
was too large but the bound said it must be small. Here the situation
is different: the *constructors themselves* don't match (like `0 = 1`),
and a simpler pattern handles this case.

How do you prove `a ≠ b` for `Fin` elements? In Lean, `a ≠ b` is
defined as `a = b → False` — a function that takes an equality proof
and derives a contradiction.

The strategy is:
1. `intro h` — assume `a = b` (giving `h : a = b`)
2. `cases h` — Lean checks if the constructors match; if the underlying
   values differ, it closes the goal automatically

When `h : ⟨a, _⟩ = ⟨b, _⟩` and `a ≠ b` as natural numbers, `cases h`
performs *injection* — it sees the values inside the constructors don't
match and derives a contradiction. This is the same idea as `Fin.ext_iff`
in reverse: if the values differ, the elements can't be equal.

**Your task**: Prove that `0` and `1` are different elements of `Fin 3`.
"

/-- `0` and `1` are distinct elements of `Fin 3`. -/
Statement : (0 : Fin 3) ≠ 1 := by
  Hint "Remember, `≠` means `= → False`. Start with `intro h`
  to assume they are equal."
  intro h
  Hint "Now `{h}` says these `Fin` elements are equal. But their
  underlying values are `0` and `1` — different natural numbers.
  `cases h` performs injection and sees the contradiction."
  Hint (hidden := true) "Try `cases h`."
  cases h

Conclusion "
The pattern for proving `a ≠ b` on `Fin` elements is:
```
intro h
cases h
```

This is called **constructor discrimination**: when `cases` examines
an equality `h : ⟨a, _⟩ = ⟨b, _⟩`, it performs *injection* (extracts
that `a = b`) and then checks whether this is consistent. When `a`
and `b` are distinct constructors (like `Nat.zero` and `Nat.succ _`),
the equality is impossible, and the goal closes automatically. This
pattern works for any type with distinct constructors — `Nat`, `Bool`,
`Fin`, etc. — not just `Fin`.

You could also prove this using `Fin.ext_iff`: `intro h; rw [Fin.ext_iff] at h; omega`.
This reduces the `Fin` equality to `0 = 1` at the `ℕ` level, then
`omega` sees the contradiction. Both approaches work — here's when
to choose each:

- **`intro h; cases h`** — use when both sides are **concrete literals**
  (like `0` and `1`). The constructor discrimination is automatic.
- **`intro h; rw [Fin.ext_iff] at h; omega`** — use when either side
  involves a **variable** or **arithmetic expression** (like `i` or
  `i + 1`). The `cases` approach won't fire on variable expressions,
  but reducing to values and using `omega` always works.

This is the discrimination step you'll need in the boss.

**Looking ahead**: The fact that Lean can *computationally* determine
whether two `Fin` elements are equal is called **decidable equality**.
The `intro h; cases h` pattern works because Lean's kernel can evaluate
whether the underlying constructors match. This property — `DecidableEq
(Fin n)` — is what will make `Finset (Fin n)` possible in Phase 2: a
finite set needs to check for duplicates, and decidable equality is what
makes that check computable.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
