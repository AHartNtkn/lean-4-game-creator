import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 7

Title "Transfer: Subset cardinality"

Introduction
"
# Transfer: A subset-cardinality argument

In ordinary mathematics, the following is immediate:

> If A ⊆ B, then |A| ≤ |B|.

In Lean, this is `Finset.card_le_card`. Your task is to apply it
in a concrete setting and then see the paper translation.

## Your task

Given the hypothesis `h : {100, 200} ⊆ {100, 200, 300, 400}`,
prove `({100, 200} : Finset Nat).card ≤ ({100, 200, 300, 400} : Finset Nat).card`.
"

/-- Subset implies cardinality inequality, for large-valued finsets. -/
Statement (h : ({100, 200} : Finset Nat) ⊆ {100, 200, 300, 400}) :
    ({100, 200} : Finset Nat).card ≤ ({100, 200, 300, 400} : Finset Nat).card := by
  Hint (hidden := true) "Use `exact Finset.card_le_card h`."
  exact Finset.card_le_card h

Conclusion
"
You applied `Finset.card_le_card` to convert a subset relation into
a cardinality inequality. Now the paper version:

## The paper argument

> **Claim**: If A ⊆ B, then |A| ≤ |B|.
>
> **Proof**: Let A = {100, 200} and B = {100, 200, 300, 400}.
> Since every element of A is also an element of B (both 100 and 200
> appear in B), we have A ⊆ B. A subset cannot have more elements
> than the set containing it, so |A| = 2 ≤ 4 = |B|.

**The key principle**: A subset has at most as many elements as the
set it is contained in. This is so basic that in paper mathematics
it is often used without comment. In Lean, it requires the explicit
lemma `Finset.card_le_card`.

**Transfer check**: You can now state and apply the subset-cardinality
principle in both formal and informal settings. This introduces T3.
"

DisabledTactic trivial decide native_decide aesop simp_all
