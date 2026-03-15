import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 2

Title "Filter membership: both directions"

Introduction
"
# Proving and disproving filter membership

In the last level you showed an element **is** in a filtered finset.
Now you will prove that an element is **not** in a filtered finset.

Recall the key lemma:
```
Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a
```

To show `a ∉ s.filter p`, you need to show that the conjunction fails:
either `a ∉ s` or `¬ p a`.

## Your task

Prove that `3` does **not** belong to the even elements of
{1, 2, 3, 4, 5}.

**Strategy**: Rewrite with `Finset.mem_filter`, introduce the
assumption, then extract the part `3 % 2 = 0` and show it is false.
"

/-- `3` is not among the even elements of `{1, 2, 3, 4, 5}`. -/
Statement : (3 : Nat) ∉ Finset.filter (fun x => x % 2 = 0) {1, 2, 3, 4, 5} := by
  Hint "The goal is a negation: `3 ∉ ...`. This means you need to
  show the membership is false. Start by rewriting with
  `Finset.mem_filter`."
  Hint (hidden := true) "Use `rw [Finset.mem_filter]`."
  rw [Finset.mem_filter]
  Hint "The goal is now a negation of a conjunction. Introduce this
  as a hypothesis to derive a contradiction."
  Hint (hidden := true) "Use `intro h`."
  intro h
  Hint "Now `h` is the conjunction. Extract the second part (the
  predicate) since that is the false part."
  Hint (hidden := true) "Use `rcases h with ⟨_, hp⟩`."
  rcases h with ⟨_, hp⟩
  Hint "You have `hp : 3 % 2 = 0`, but `3 % 2 = 1 ≠ 0`. Use `norm_num`
  to close this."
  Hint (hidden := true) "Use `norm_num at hp`."
  norm_num at hp

Conclusion
"
You proved a non-membership result for a filtered finset.

The proof followed a common pattern for negated filter membership:

1. **Rewrite** with `Finset.mem_filter` to see the conjunction.
2. **Assume** the conjunction holds (by `intro`).
3. **Extract** the false part and derive a contradiction.

This is really just propositional reasoning: `¬ (A ∧ B)` when `¬ B`.

**Tip**: When the predicate involves arithmetic, `norm_num` is usually
the right tool to close the contradiction.
"

DisabledTactic trivial decide native_decide aesop simp_all
