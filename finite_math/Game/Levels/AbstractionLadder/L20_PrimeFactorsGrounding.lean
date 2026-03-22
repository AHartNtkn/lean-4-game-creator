import Game.Metadata

World "AbstractionLadder"
Level 20

Title "Grounding: Prime Factors of 12"

Introduction "
# The Ladder in Mathematics: Prime Factorization

So far, the lists in this world have been abstract: `[1, 2, 3]` or
`[a, b, c]`. But the abstraction ladder captures real mathematical
distinctions. Consider the prime factorization of 12:

$$12 = 2 \\times 2 \\times 3$$

The factorization can be represented at each layer:

| Layer | Representation | What it captures |
|---|---|---|
| **List** | `[2, 2, 3]` | An ordered sequence of prime factors |
| **Multiset** | `{2, 2, 3}` | The prime factorization (multiplicity matters) |
| **Finset** | `{2, 3}` | The set of prime divisors |

Each layer answers a different question:
- **List**: 'What are the factors, in this specific order?'
  `[2, 2, 3]` and `[2, 3, 2]` are different lists.
- **Multiset**: 'What is the prime factorization?'
  The same multiset regardless of how you order the factors.
- **Finset**: 'Which primes divide 12?'
  Just the set of distinct primes that appear.

**Your task**: Prove that the two list representations `[2, 2, 3]`
and `[2, 3, 2]` give the same multiset. This captures the fact that
the prime factorization doesn't depend on the order you write the
factors.
"

/-- Two orderings of the prime factors of 12 give the same multiset. -/
Statement : (↑[2, 2, 3] : Multiset ℕ) = ↑[2, 3, 2] := by
  Hint "Convert the multiset equality to a list permutation using
  `Multiset.coe_eq_coe`."
  rw [Multiset.coe_eq_coe]
  Hint "Now prove `[2, 2, 3] ~ [2, 3, 2]`. The first element `2` is
  the same on both sides, so use `List.Perm.cons` for the head.
  The tails `[2, 3]` and `[3, 2]` differ by a single swap."
  Hint (hidden := true) "Try:
  `exact List.Perm.cons 2 (List.Perm.swap 3 2 [])`"
  exact List.Perm.cons 2 (List.Perm.swap 3 2 [])

Conclusion "
You proved that `[2, 2, 3]` and `[2, 3, 2]` give the same multiset —
the prime factorization of 12 doesn't depend on the order.

This is the abstraction ladder applied to a real mathematical object:

| What you want to know | Layer | Answer |
|---|---|---|
| The factors in a specific order | List `[2, 2, 3]` | Depends on ordering convention |
| The prime factorization | Multiset | Unique (fundamental theorem of arithmetic) |
| Which primes divide 12 | Finset `{2, 3}` | Just the distinct primes |

The three types are not just Lean plumbing — they capture genuine
mathematical distinctions. When a number theorist writes '2^2 x 3 is
the prime factorization of 12', they are working at the multiset level:
the multiplicity of each prime matters, but the order doesn't.

**When to use which layer**:
- Use a **list** when order matters (sequences, paths, algorithms)
- Use a **multiset** when multiplicity matters but order doesn't
  (prime factorizations, polynomial roots with multiplicity)
- Use a **finset** when only membership matters (support of a function,
  set of divisors, domain of a partial map)
"

TheoremTab "Multiset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
