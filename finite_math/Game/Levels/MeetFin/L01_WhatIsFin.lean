import Game.Metadata

World "MeetFin"
Level 1

Title "What is Fin n?"

Introduction "
# What is `Fin n`?

In mathematics, we often work with finite index sets like
$\\{0, 1, 2, 3, 4\\}$ — the first $n$ natural numbers.

In Lean 4, this is captured by the type `Fin n`. An element of `Fin n`
is a natural number `k` **together with a proof** that `k < n`.

More precisely:
$$\\texttt{Fin } n = \\{ k : \\mathbb{N} \\mid k < n \\}$$

**Why not just use `ℕ`?** If you index a length-5 vector with a plain
natural number, nothing stops you from using `7` — the type checker
can't tell it's out of bounds. With `Fin 5`, the bound is part of the
type: you literally *cannot construct* an element unless you prove it's
in range. The type system enforces the constraint for you.

You might wonder why `Fin n` starts at 0 rather than 1.
Zero-indexing means the values of `Fin n` are exactly the natural
numbers less than `n`, which aligns with how Lean indexes lists and
arrays. It also means `Fin n` has a natural 'zero' element when
`n > 0`.

This is an example of a *subtype* — a type carved out of a larger type
by a predicate. `Fin n` is the subtype `{ k : ℕ // k < n }`.

To construct an element of `Fin n`, use the **anonymous constructor**
`⟨k, proof⟩`, where:
- `k` is the natural number
- `proof` shows `k < n`

For the proof part, the `omega` tactic handles routine arithmetic
goals like `3 < 5`.

**Your task**: Construct any element of `Fin 5`. There are five to
choose from: $0, 1, 2, 3, 4$.

Try `exact ⟨3, by omega⟩`.

*Notation*: type `⟨` as `\\langle` and `⟩` as `\\rangle`.

**Important**: Lean happens to accept `exact 3` for this level
because it can figure out the bound automatically when it's a
concrete number like `5`. But this shortcut will **stop working**
starting at Level 12, when the bound becomes a variable `n`.
Practice `⟨k, by omega⟩` now — it's the pattern that always works.
"

-- INTENTIONAL DESIGN EXCEPTION (P0-1 accepted):
-- The goal type `Fin 5` allows `exact 0`, `exact 3`, etc. via Lean's
-- OfNat coercion. This is deliberately accepted as an onboarding choice:
--
-- Rationale: This is the very first level of the entire course. Forcing
-- the constructor pattern (e.g. via a variable bound or subtype wrapper)
-- would introduce additional complexity that overwhelms true beginners.
-- The introduction explicitly teaches `⟨k, by omega⟩` and asks the
-- learner to use it. The conclusion explicitly warns that the shortcut
-- (`exact 3`) only works for concrete bounds and that the explicit
-- constructor becomes mandatory from Level 12 onward.
--
-- The pedagogical contract: the level TEACHES the pattern without
-- FORCING it. The learner who follows instructions learns the right
-- skill; the learner who discovers the shortcut gets a preview of
-- Lean's coercion system, which is itself educational.
--
-- Alternatives considered and rejected:
-- - Variable bound (`Fin (n+1)`): `exact 0` still works via Zero instance
-- - Subtype wrapper (`{ i : Fin 5 // i.val = 3 }`): too complex for L01
-- - Disabling OfNat: not possible via DisabledTheorem

/-- Constructs a specific element of `Fin 5`. -/
Statement : Fin 5 := by
  Hint "Use the anonymous constructor `⟨k, by omega⟩` where `k` is any
  natural number less than 5. For example, `exact ⟨3, by omega⟩`."
  exact ⟨3, by omega⟩

Conclusion "
Well done! You just constructed the element $3$ as a term of type
`Fin 5`.

The key pattern: to build a `Fin n`, you provide **two things** — a
number and a proof that it's in range. The `⟨k, by omega⟩` idiom
will appear throughout this world.

In ordinary mathematics, saying *let $x = 3 \\in \\{0, \\ldots, 4\\}$*
is informal. In Lean, you must **prove** the element is in range.
That's what the second component does.

**Design note**: `exact 3` also works here — Lean can automatically
coerce a numeric literal into `Fin 5` when the bound is known.
We intentionally allow this shortcut in this first level so you can
focus on understanding the *structure* of `Fin` without getting stuck
on syntax. But practice the `⟨k, by omega⟩` pattern now, because
starting in Level 12, the type bound will be a variable `n` — not a
concrete number — and the automatic coercion won't work. The explicit
constructor is the general-purpose tool.
"

/-- `omega` closes goals involving linear arithmetic over `ℕ` and `ℤ`.
It handles equalities (`=`), inequalities (`<`, `≤`, `≥`, `>`),
and negated equalities (`≠`).

## Syntax
```
omega
```

## When to use it
- When the goal follows from linear arithmetic: `3 < 5`, `n + 1 ≤ m`
- When hypotheses contradict each other: if you have `h1 : x = 5` and
  `h2 : x < 5`, omega sees the contradiction and closes any goal
- When multiple hypotheses combine: omega reasons across ALL hypotheses
  simultaneously, not just one at a time

## Examples
```
-- Goal: 3 < 5
omega

-- h1 : x = 5, h2 : x < 5 → closes any goal (contradiction)
omega

-- h1 : a ≤ b, h2 : b < c → Goal: a < c
omega
```

## Warning
`omega` only handles *linear* arithmetic. It cannot solve goals
involving multiplication of variables (like `n * m < n * n + 1`).
-/
TacticDoc omega

/-- `Fin n` is the type of natural numbers strictly less than `n`.

An element of `Fin n` consists of:
- `val : ℕ` — the underlying natural number
- `isLt : val < n` — a proof that the number is in range

`Fin n` is the subtype `{ k : ℕ // k < n }`.

## Construction
Use the anonymous constructor: `⟨k, proof⟩`

## Example
`⟨3, by omega⟩ : Fin 5` — the number 3 with a proof that `3 < 5`.

## Warning
`Fin n` has elements `0, 1, ..., n-1` (NOT `1, ..., n`).
`Fin 0` is **empty** — there is no natural number less than 0.
-/
DefinitionDoc Fin as "Fin"

/-- `Fin.mk val isLt` constructs an element of `Fin n` from a natural
number `val` and a proof `isLt : val < n`.

Equivalently, use the anonymous constructor `⟨val, isLt⟩`.

## Example
`⟨3, by omega⟩ : Fin 5`
-/
DefinitionDoc Fin.mk as "Fin.mk"

NewTactic omega exact rw intro cases «have» use left right rfl constructor apply
NewDefinition Fin Fin.mk

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
