import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 4

Title "Filter and cardinality"

Introduction
"
# Filter and cardinality

Compute the cardinality of a filtered finset on fresh data.

The finset `{2, 4, 6, 8, 10}` contains five numbers. Filtering
by the predicate `x > 5` keeps only `{6, 8, 10}` — three elements.

Prove that the cardinality of the filtered finset is `3`.

## Strategy

First show that the filter of the finset equals the finset of elements
greater than 5, using `ext` and membership reasoning. Then compute the
cardinality of the result.

Alternatively, use `simp` with the appropriate lemmas to identify the
filter result, then compute.
"

/-- The elements of `{2, 4, 6, 8, 10}` greater than 5 form a finset of size 3. -/
Statement : (Finset.filter (fun x => x > 5) ({2, 4, 6, 8, 10} : Finset Nat)).card = 3 := by
  Hint (hidden := true) "One approach: use `have` to show the filter
  equals the expected finset, then `rw` and compute."
  have h : Finset.filter (fun x => x > 5) ({2, 4, 6, 8, 10} : Finset Nat) = {6, 8, 10} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [h]; rfl

Conclusion
"
You computed the cardinality of a filtered finset on fresh data.
The key steps were:

1. Identify what the filter produces (using `ext` + membership).
2. Compute the cardinality of the resulting finset.

**Retrieval check**: This level retrieved filter reasoning (M8) and
cardinality computation (M9) on a new finset.
"

DisabledTactic trivial decide native_decide aesop simp_all
