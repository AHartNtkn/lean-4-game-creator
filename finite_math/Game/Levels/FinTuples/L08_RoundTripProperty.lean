import Game.Metadata

World "FinTuples"
Level 8

Title "The Round Trip"

Introduction "
# Cons and Decompose Are Inverses

In Level 7, you proved that decomposing a tuple into head + tail
and reassembling gives back the original:

$$\\texttt{Fin.cons}\\;(f\\;0)\\;(\\texttt{Fin.tail}\\;f) = f \\quad (\\texttt{Fin.cons\\_self\\_tail})$$

But a true inverse relationship goes both ways. The reverse
direction asks: if you START with a head `a` and a tail `g`,
cons them together, and then decompose — do you get back `a`
and `g`?

Concretely:
- `(Fin.cons a g) 0 = a` — the head of the assembled tuple is `a`
- `Fin.tail (Fin.cons a g) = g` — the tail of the assembled tuple is `g`

Together with Level 7, this shows that `Fin.cons` and `(head, tail)`
are genuine inverse operations — a bijection between
`α × (Fin n → α)` and `Fin (n + 1) → α`.

**Your task**: Prove both round-trip properties. Use `rw [hg]`
to substitute the hypothesis, then the access lemma or `ext`.
"

/-- Assembling and decomposing recovers the original components. -/
Statement (a : ℕ) (g : Fin 2 → ℕ) (h : Fin 3 → ℕ) (hh : h = Fin.cons a g) :
    h 0 = a ∧ Fin.tail h = g := by
  Hint "Use `constructor` to split the conjunction."
  constructor
  · Hint "The goal is `h 0 = a`. Rewrite `h` using `hh`, then
    simplify: `rw [hh, Fin.cons_val_zero]`."
    rw [hh, Fin.cons_val_zero]
  · Hint "The goal is `Fin.tail h = g`. After `rw [hh]`, the
    goal becomes `Fin.tail (Fin.cons a g) = g`.
    Use `ext i` to check pointwise, then `rfl`."
    rw [hh]
    Hint "Now use `ext i` to reduce function equality to
    pointwise equality."
    ext i
    Hint "The goal `Fin.tail (Fin.cons a g) i = g i` holds
    because `Fin.tail` evaluates at `i.succ`, and
    `Fin.cons a g i.succ = g i` by definition. Use `rfl`."
    rfl

Conclusion "
The round-trip is now complete. `Fin.cons` and `(head, tail)` are
genuine inverses:

| Direction | Identity |
|---|---|
| Decompose then reassemble | `Fin.cons (f 0) (Fin.tail f) = f` |
| Assemble then decompose (head) | `(Fin.cons a g) 0 = a` |
| Assemble then decompose (tail) | `Fin.tail (Fin.cons a g) = g` |

This means `Fin (n + 1) → α` is in bijection with
`α × (Fin n → α)` — an `(n+1)`-tuple is exactly a head
element plus an `n`-tuple. This decomposition is the foundation
for reasoning about tuples by induction on length.

Next, you'll learn the dual construction: appending an element
at the *end* of a tuple using `vecSnoc`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
