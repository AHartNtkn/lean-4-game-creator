import GameServer.Commands
import Mathlib

World "ListBasics"
Level 4

Title "Membership in an append"

Introduction
"
# Appending lists and membership

`List.append l₁ l₂` (written `l₁ ++ l₂`) concatenates two lists -- it
puts all elements of `l₁` followed by all elements of `l₂`.

For example:
- `[1, 2] ++ [3, 4] = [1, 2, 3, 4]`
- `[] ++ l = l`
- `l ++ [] = l`

## Membership in an append

The key fact about membership in appended lists is:
```
List.mem_append : a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂
```

An element belongs to `l₁ ++ l₂` if and only if it belongs to `l₁` or
it belongs to `l₂`.

## Your task

Given that `a ∈ l₁`, prove that `a ∈ l₁ ++ l₂`.

Since `a ∈ l₁`, we know `a ∈ l₁ ∨ a ∈ l₂` holds (left disjunct), so
`a ∈ l₁ ++ l₂` by the characterization above.

**Strategy**:
1. `rw [List.mem_append]` to unfold membership in the append
2. `left` to choose the left disjunct
3. `exact h` to use the hypothesis
"

/-- If `a` is in `l₁`, then `a` is in `l₁ ++ l₂`. -/
Statement (a : Nat) (l₁ l₂ : List Nat) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ := by
  Hint "The goal is `a ∈ l₁ ++ l₂`. Unfold membership in the append
  using `rw [List.mem_append]`."
  rw [List.mem_append]
  Hint "The goal is now `a ∈ l₁ ∨ a ∈ l₂`. You know `a ∈ l₁` from the
  hypothesis `h`. Use `left` to select the left disjunct."
  left
  Hint "Now the goal is `a ∈ l₁`, which is exactly hypothesis `h`.
  Use `exact h`."
  exact h

DisabledTactic decide native_decide simp aesop

Conclusion
"
You proved that membership in the first list implies membership in the
concatenation. The proof unfolded `a ∈ l₁ ++ l₂` into `a ∈ l₁ ∨ a ∈ l₂`,
chose the left side, and used the hypothesis.

Notice the similarity to the previous level: once you unfold the
membership condition, the structure of the proof is about `∨` -- choosing
which disjunct to verify. This is a recurring pattern in list proofs.

The symmetric fact also holds: if `a ∈ l₂`, then `a ∈ l₁ ++ l₂` (choosing
the right disjunct instead). Together, these give the full `↔`.

**Key properties of append**:
- `(l₁ ++ l₂).length = l₁.length + l₂.length`
- `a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂`
- Append is associative: `(l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃)`

**In plain language**: \"If an element appears in a list, it still appears
when you extend that list by appending more elements at the end.\"
"

/-- `List.append l₁ l₂` (written `l₁ ++ l₂`) concatenates two lists. All
elements of `l₁` come first, followed by all elements of `l₂`.

Key properties:
- `(l₁ ++ l₂).length = l₁.length + l₂.length`
- `a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂`
- `(l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃)` -/
DefinitionDoc List.append as "List.append"

/-- `List.mem_append` states that `a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂`.
An element is in a concatenation iff it is in one of the two pieces. -/
TheoremDoc List.mem_append as "List.mem_append" in "List"

NewDefinition List.append
NewTheorem List.mem_append
