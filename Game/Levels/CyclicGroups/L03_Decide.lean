import Game.Metadata

World "CyclicGroups"
Level 3

Title "The decide Tactic"

Introduction
"
Later in this world, you'll prove that groups of **prime** order are
cyclic. To use results about primes, you sometimes need to verify
that a specific number is prime.

Is `5` prime? You could check by hand: it's not divisible by `2`,
`3`, or `4`, so yes. But Lean can do this check automatically with
the `decide` tactic.

`decide` works on any **decidable** proposition — a statement whose
truth value can be determined by computation. This includes:

- `Nat.Prime 5` (is 5 prime?)
- `(3 : ℕ) ≠ 0` (is 3 nonzero?)
- `2 < 7` (is 2 less than 7?)
- equality and inequality of concrete natural numbers

For abstract mathematical objects (like an arbitrary group `G`),
`decide` usually can't help — those require proof. But for concrete
computations, it's the right tool.

Prove that `5` is prime.
"

/-- The `decide` tactic closes goals that are **decidable** — their
truth can be verified by computation.

Common uses:
- `Nat.Prime 5` — verify a number is prime
- `(3 : ℕ) ≠ 0` — verify a number is nonzero
- `2 < 7` — verify a numeric inequality

`decide` works only on concrete, computable propositions. It cannot
prove statements about abstract mathematical objects.

Just type `decide` with no arguments. -/
TacticDoc decide

NewTactic decide

DisabledTactic group

Statement : Nat.Prime 5 := by
  Hint "The goal is `Nat.Prime 5`. This is a decidable proposition —
  Lean can check it by computation. Use `decide`."
  decide

Conclusion
"
The `decide` tactic verified `Nat.Prime 5` by computation. It checked
that `5` is greater than `1` and not divisible by any smaller number.

`decide` is a special tactic: it doesn't require you to construct a
proof. Instead, it runs an algorithm that computes the answer. This
works because `Nat.Prime` is a *decidable* predicate on natural
numbers.

You'll encounter `decide` again when working with concrete finite
groups and permutations in later worlds. For now, the key takeaway
is: when a goal is a concrete computation, `decide` can close it.
"
