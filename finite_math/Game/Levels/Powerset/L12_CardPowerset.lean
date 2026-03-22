import Game.Metadata

World "Powerset"
Level 12

Title "Counting Subsets: 2^n"

Introduction "
# How Many Subsets?

A set with $n$ elements has $2^n$ subsets. This is one of the most
fundamental facts in combinatorics.

The intuition: for each of the $n$ elements, you independently
choose *in* or *out* — that's 2 choices per element, giving
$2 \\times 2 \\times \\cdots \\times 2 = 2^n$ total subsets.

In Lean, this is:

`Finset.card_powerset : (s.powerset).card = 2 ^ s.card`

**Your task**: Given a finset `s` with `s.card = 3`, prove that
`s.powerset` has 8 elements. Use `card_powerset` to relate the
powerset size to $2^n$, then substitute the card.
"

/-- `Finset.card_powerset` states that
`(s.powerset).card = 2 ^ s.card`.

## Syntax
```
rw [Finset.card_powerset]
```

## When to use it
When you see `(s.powerset).card` in a goal or hypothesis and want
to replace it with `2 ^ s.card`.

## Meaning
A finset with `n` elements has exactly `2^n` subsets.

## Example
If `s.card = 4`, then `(s.powerset).card = 2^4 = 16`.
-/
TheoremDoc Finset.card_powerset as "Finset.card_powerset" in "Finset"

/-- A 3-element finset has 8 subsets. -/
Statement (s : Finset ℕ) (hs : s.card = 3) : (s.powerset).card = 8 := by
  Hint "The goal asks for the cardinality of `s.powerset`. Use `have`
  to bring `card_powerset` into the context as a hypothesis."
  Hint (hidden := true) "Try `have h := Finset.card_powerset s`."
  have h := Finset.card_powerset s
  Hint "Now `h : (s.powerset).card = 2 ^ s.card`. Substitute `s.card`
  in `h` to `3` using `hs`."
  Hint (hidden := true) "Try `rw [hs] at h`."
  rw [hs] at h
  Hint "Now `h : (s.powerset).card = 2 ^ 3` and the goal is
  `(s.powerset).card = 8`. Since $2^3 = 8$, `h` matches the goal."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
Three steps: `have h := card_powerset s`, `rw [hs] at h`, `exact h`.

The `have` brings `card_powerset` into the context. Then `rw [hs] at h`
substitutes the known card value. Finally `exact h` closes the goal
because Lean computes $2^3 = 8$ automatically.

**A useful table**:
| Elements ($n$) | Subsets ($2^n$) |
|:-:|:-:|
| 0 | 1 |
| 1 | 2 |
| 2 | 4 |
| 3 | 8 |
| 4 | 16 |
| 5 | 32 |

This exponential growth is why brute-force subset enumeration
quickly becomes impractical — and why we need structural results
like the binomial coefficient to count subsets of a specific size.

**Shortcut**: You can also do this in one step with
`rw [Finset.card_powerset, hs]` — a single rewrite that applies
`card_powerset` and then substitutes `hs` in one go. The `have`
pattern is more general (you'll use it whenever the rewrite target
is buried inside a larger expression), but the direct `rw` is
sometimes simpler.

**Why $2^n$?** Each subset corresponds to a function from $s$ to
'in or out' — a binary choice per element. These functions are
called **indicator functions** (or characteristic functions).
The set of all indicator functions on an $n$-element set has
$2^n$ elements, one for each possible subset. In the
CountingTechniques world, you will formalize this bijection by
proving that the set of functions `s -> Fin 2` has cardinality
`2 ^ s.card`.
"

NewTheorem Finset.card_powerset

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
