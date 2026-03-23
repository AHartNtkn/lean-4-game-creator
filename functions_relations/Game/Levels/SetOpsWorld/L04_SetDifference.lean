import Game.Metadata

World "SetOpsWorld"
Level 4

Title "Set Difference"

Introduction "
# Set Difference: \\ means ∧ ¬

The **set difference** `s \\ t` contains elements in `s` that are
NOT in `t`:

$$x \\in s \\setminus t \\;\\;\\Longleftrightarrow\\;\\; x \\in s \\;\\land\\; x \\notin t$$

This combines conjunction and negation: you must be IN the first set
AND NOT IN the second.

To prove `x ∈ s \\ t`:
1. `constructor` — split into two goals (`x ∈ s` and `x ∉ t`)
2. Prove `x ∈ s` (the positive part)
3. Prove `x ∉ t` (the negative part: `intro` then contradiction)

**Your task**: Prove that 3 is in the set of numbers less than 10 but
not even. This requires: $3 < 10$ (true) and $3$ is not even (true).
"

/-- 3 is less than 10 and not even. -/
Statement : (3 : ℕ) ∈ ({n : ℕ | n < 10} \ {n | Even n}) := by
  Hint "The goal is a set difference membership, which means a conjunction
  of membership and non-membership. Use `constructor` to split it."
  Branch
    show 3 < 10 ∧ ¬ Even 3
    constructor
    · omega
    · intro h
      obtain ⟨r, hr⟩ := h
      omega
  constructor
  -- First goal: 3 < 10
  · Hint "Prove that 3 is in the first set. Use `show 3 < 10` then `omega`."
    Hint (hidden := true) "`show 3 < 10` then `omega`."
    show 3 < 10
    omega
  -- Second goal: 3 ∉ {n | Even n}
  · Hint "Prove that 3 is NOT in the second set. This means
    `Even 3 → False`. Use `intro h` to assume `Even 3`, then derive
    a contradiction."
    Hint (hidden := true) "`intro h` then `obtain ⟨r, hr⟩ := h` then `omega`."
    intro h
    Hint "Destructure `h : Even 3` with `obtain ⟨r, hr⟩ := h`, then
    `omega` finds the contradiction."
    obtain ⟨r, hr⟩ := h
    omega

Conclusion "
You now know all four set operations:

| Operation | Notation | Logic | Proof tactic |
|---|---|---|---|
| Union | `s ∪ t` | `x ∈ s ∨ x ∈ t` | `left` / `right` |
| Intersection | `s ∩ t` | `x ∈ s ∧ x ∈ t` | `constructor` |
| Complement | `sᶜ` | `¬ (x ∈ s)` | `intro h`, then contradiction |
| Difference | `s \\ t` | `x ∈ s ∧ x ∉ t` | `constructor`, then prove each |

Every set operation reduces to propositional logic. This is the
central design principle of Lean's set library: there is no special
set-theoretic machinery. All set reasoning IS logical reasoning.

Note that set difference combines intersection and complement:
`s \\ t = s ∩ tᶜ`. You will prove this identity in the next level.

**Fun fact**: The **symmetric difference** `s Δ t = (s \\ t) ∪ (t \\ s)`
contains elements in exactly one of the two sets. With this operation,
the subsets of any type form an abelian group (with identity `∅`).
We will not prove this in this course, but it is a fascinating
structural fact worth knowing.
"

/-- `s \\ t` (typed `\\setminus` or `\\\\`) is the **set difference**:
elements in `s` that are NOT in `t`.

$$x \\in s \\setminus t \\iff x \\in s \\land x \\notin t$$

## Proof strategies

**To prove** `x ∈ s \\ t`:
- `constructor` then prove `x ∈ s` and `x ∉ t` separately

**Given** `h : x ∈ s \\ t`:
- `h.1 : x ∈ s` and `h.2 : x ∉ t` (dot projection)
- `obtain ⟨hs, ht⟩ := h` (destructuring)

## Example
`3 ∈ {n | n < 10} \\ {n | Even n}` reduces to `3 < 10 ∧ ¬ Even 3`.

## Related
`s \\ t = s ∩ tᶜ` — difference is intersection with complement.
-/
DefinitionDoc Set.diff as "Set.diff"

NewDefinition Set.diff

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
