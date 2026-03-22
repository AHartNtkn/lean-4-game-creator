import Game.Metadata

World "FinsetBasics"
Level 15

Title "Nonempty Finsets"

Introduction "
# Finset.Nonempty

A finset `s` is **nonempty** if it has at least one element. In Lean,
this is defined as:

$$\\texttt{s.Nonempty} \\;=\\; \\exists\\, x,\\; x \\in s$$

This is an *existential statement* — it asserts that some element
exists in `s` without naming which one. When you have a hypothesis
`hs : s.Nonempty`, you can **extract** a concrete element using
`obtain`:

```
obtain ⟨x, hx⟩ := hs
-- now x : α and hx : x ∈ s are in the context
```

This is the same `obtain` pattern you learned in the Fin pset for
destructuring existentials. Here, it extracts an element and its
membership proof from a nonemptiness hypothesis.

**Your task**: Given a nonempty finset `s` where every element is
less than 100, find an element of `s` that is less than 100.

The goal `∃ y ∈ s, y < 100` asks for a `y` that is both in `s` AND
less than 100. You must extract a witness from `hs` — you can't just
pick any number less than 100, because it also needs to be in `s`.

Extract a witness from `hs : s.Nonempty`, then use it to satisfy
both requirements.
"

/-- Extract a bounded element from a nonempty finset with a bound. -/
Statement (s : Finset ℕ) (hs : s.Nonempty) (hbound : ∀ x ∈ s, x < 100) :
    ∃ y ∈ s, y < 100 := by
  Hint "Extract an element from `{hs}` using
  `obtain ⟨x, hx⟩ := hs`. This gives you `x : ℕ` and `hx : x ∈ s`."
  obtain ⟨x, hx⟩ := hs
  Hint "Now you have `x` in `s` and need to show `∃ y ∈ s, y < 100`.
  Provide `x` as the witness with `use x`."
  use x
  Hint "The goal is `x ∈ s ∧ x < 100`. Split the conjunction with
  `constructor`."
  Hint (hidden := true) "After `constructor`, prove each part separately:
  `exact {hx}` for membership and `exact {hbound} x {hx}` for the bound."
  constructor
  · Hint "The goal is `x ∈ s`. You already have `{hx} : x ∈ s`."
    Hint (hidden := true) "`exact {hx}`"
    exact hx
  · Hint "The goal is `x < 100`. Apply the bound hypothesis to your
    specific element: `exact {hbound} x {hx}`."
    Hint (hidden := true) "`exact {hbound} x {hx}`"
    exact hbound x hx

Conclusion "
The `Finset.Nonempty` extraction pattern:

1. `obtain ⟨x, hx⟩ := hs` — get a concrete element and its membership
2. Use `x` and `hx` in the rest of the proof

Since `Nonempty` is just `∃ x, x ∈ s`, this is ordinary existential
destructuring. No new tactic needed — just `obtain` applied to a
finset-level hypothesis.

**Forward direction** (proving Nonempty): To prove `s.Nonempty`, you
need to show `∃ x, x ∈ s`. Use `use a` with a specific element `a`,
then prove `a ∈ s` with the membership tools from earlier levels.
You'll practice this in the next level.

In ordinary mathematics: 'since $S$ is nonempty, pick some $x \\in S$.'
In Lean: `obtain ⟨x, hx⟩ := hs`.
"

/-- `Finset.Nonempty s` means the finset `s` has at least one element.

Defined as `∃ a, a ∈ s`.

## Extracting an element
Given `hs : s.Nonempty`:
```
obtain ⟨x, hx⟩ := hs
-- x : α, hx : x ∈ s
```

## Proving Nonempty
To prove `s.Nonempty` for a concrete finset:
```
use a               -- provide a specific element
-- remaining goal: a ∈ s
```

## When to use it
When you need to reason about finsets having elements — e.g., to
apply a universally quantified property to at least one element.
-/
DefinitionDoc Finset.Nonempty as "Finset.Nonempty"

NewDefinition Finset.Nonempty

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
