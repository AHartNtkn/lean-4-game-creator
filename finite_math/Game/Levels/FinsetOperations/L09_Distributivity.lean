import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 9

Title "Distributivity"

Introduction
"
# Intersection distributes over union

This level combines `ext`, membership lemmas, and `by_cases` in a
longer proof. You will prove a fundamental set-algebraic identity:

```
s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)
```

This is **distributivity of intersection over union** -- the set-theory
analogue of `a × (b + c) = a × b + a × c`.

## Proof plan

1. Use `ext a` to reduce to membership.
2. Use `constructor` to split the biconditional.
3. **Forward direction** (`→`): Given `a ∈ s ∩ (t ∪ u)`, extract
   `a ∈ s` and `a ∈ t ∪ u`. Case-split on the union to determine
   whether `a ∈ t` or `a ∈ u`, and place `a` in the appropriate
   part of the right side.
4. **Reverse direction** (`←`): Given `a ∈ (s ∩ t) ∪ (s ∩ u)`,
   case-split on which part of the union `a` came from, and show
   `a ∈ s ∩ (t ∪ u)` in each case.

This is a longer proof, but every step uses tools you have already
practiced.
"

/-- Intersection distributes over union. -/
Statement (s t u : Finset Nat) :
    s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  Hint "Start with `ext a` to reduce the equality to a membership
  biconditional."
  Hint (hidden := true) "Use `ext a`."
  ext a
  Hint "Split the biconditional with `constructor`."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · -- Forward direction: a ∈ s ∩ (t ∪ u) → a ∈ (s ∩ t) ∪ (s ∩ u)
    Hint "Introduce the hypothesis."
    Hint (hidden := true) "Use `intro h`."
    intro h
    Hint "Rewrite `h` with `mem_inter` to get a conjunction."
    Hint (hidden := true) "Use `rw [Finset.mem_inter] at h`."
    rw [Finset.mem_inter] at h
    Hint "Split the conjunction to extract the two parts."
    Hint (hidden := true) "Use `rcases h with ⟨hs, htu⟩`."
    rcases h with ⟨hs, htu⟩
    Hint "Now `hs : a ∈ s` and `htu : a ∈ t ∪ u`. Rewrite `htu` with
    `mem_union` and case-split on whether `a ∈ t` or `a ∈ u`."
    Hint (hidden := true) "Use `rw [Finset.mem_union] at htu`,
    then `rcases htu with ht | hu`."
    rw [Finset.mem_union] at htu
    rcases htu with ht | hu
    · Hint "Case `ht : a ∈ t`. Then `a ∈ s ∩ t`, so `a` belongs to the
      left side of the union on the right."
      Hint (hidden := true) "Use `rw [Finset.mem_union]`, `left`,
      `rw [Finset.mem_inter]`, `exact ⟨hs, ht⟩`."
      rw [Finset.mem_union]
      left
      rw [Finset.mem_inter]
      exact ⟨hs, ht⟩
    · Hint "Case `hu : a ∈ u`. Then `a ∈ s ∩ u`, so `a` belongs to the
      right side of the union."
      Hint (hidden := true) "Use `rw [Finset.mem_union]`, `right`,
      `rw [Finset.mem_inter]`, `exact ⟨hs, hu⟩`."
      rw [Finset.mem_union]
      right
      rw [Finset.mem_inter]
      exact ⟨hs, hu⟩
  · -- Reverse direction: a ∈ (s ∩ t) ∪ (s ∩ u) → a ∈ s ∩ (t ∪ u)
    Hint "Introduce the hypothesis and rewrite with `mem_union`."
    Hint (hidden := true) "Use `intro h`, then `rw [Finset.mem_union] at h`."
    intro h
    rw [Finset.mem_union] at h
    Hint "Case-split on whether `a` came from `s ∩ t` or `s ∩ u`."
    Hint (hidden := true) "Use `rcases h with hst | hsu`."
    rcases h with hst | hsu
    · Hint "Case `hst : a ∈ s ∩ t`. Extract `a ∈ s` and `a ∈ t`."
      Hint (hidden := true) "Use `rw [Finset.mem_inter] at hst`,
      `rcases hst with ⟨hs, ht⟩`."
      rw [Finset.mem_inter] at hst
      rcases hst with ⟨hs, ht⟩
      Hint "Now show `a ∈ s ∩ (t ∪ u)` using `a ∈ s` and `a ∈ t`."
      Hint (hidden := true) "Use `rw [Finset.mem_inter]`, `constructor`,
      `exact hs`, `rw [Finset.mem_union]`, `left`, `exact ht`."
      rw [Finset.mem_inter]
      constructor
      · exact hs
      · rw [Finset.mem_union]
        left
        exact ht
    · Hint "Case `hsu : a ∈ s ∩ u`. Extract `a ∈ s` and `a ∈ u`."
      Hint (hidden := true) "Use `rw [Finset.mem_inter] at hsu`,
      `rcases hsu with ⟨hs, hu⟩`."
      rw [Finset.mem_inter] at hsu
      rcases hsu with ⟨hs, hu⟩
      Hint "Now show `a ∈ s ∩ (t ∪ u)` using `a ∈ s` and `a ∈ u`."
      Hint (hidden := true) "Use `rw [Finset.mem_inter]`, `constructor`,
      `exact hs`, `rw [Finset.mem_union]`, `right`, `exact hu`."
      rw [Finset.mem_inter]
      constructor
      · exact hs
      · rw [Finset.mem_union]
        right
        exact hu

Conclusion
"
You proved **distributivity of intersection over union**! This is one
of the fundamental set-algebraic laws, and the proof showcases the
full `ext` + membership-lemma toolkit:

## Proof structure

```
ext a
constructor
· intro h            -- forward direction
  (extract pieces from h)
  (reassemble in the target)
· intro h            -- reverse direction
  (extract pieces from h)
  (reassemble in the target)
```

## What made this proof work

Every step used a tool you already knew:
- `ext` for finset equality (Level 5)
- `mem_inter` for intersection (Level 2)
- `mem_union` for union (Level 1)
- `rcases` for destructuring (from W6)
- `constructor` and `exact` for building pairs

The proof is **long** but never **hard** -- each individual step is
routine. The challenge is **organization**: keeping track of which
pieces you have and which you need.

**In plain language**: \"s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) because
an element in both s and (t ∪ u) must be in s and in either t or u,
which means it is in (s ∩ t) or (s ∩ u). Conversely, an element in
(s ∩ t) ∪ (s ∩ u) is in s and in t or u, hence in s ∩ (t ∪ u).\"
"

/-- `tauto` closes goals that are tautologies in propositional logic.

After `simp` has reduced a membership goal to a proposition involving `∧`, `∨`,
`¬`, and `↔`, `tauto` can often finish the proof by pure logical reasoning.

`tauto` is especially useful after `ext` + `simp` has reduced a finset equality
to a propositional equivalence. -/
TacticDoc tauto

NewTactic tauto
DisabledTactic trivial decide native_decide aesop simp_all
