import Game.Metadata

World "Powerset"
Level 26

Title "Symmetry of Choose via Rewriting"

Introduction "
# Rewriting with Choose Symmetry

In the BinomialCoefficients world, you used `Nat.choose_symm` with
`exact`. Now practice using it with `rw` — a pattern the boss needs.

The key new syntax: `rw [Nat.choose_symm hk]`. Notice the **proof
argument** `hk` passed inside the rewrite brackets. This tells Lean
which inequality justifies the rewrite. Without `hk`, Lean wouldn't
know that $k \\leq n$.

**Your task**: Given `hs : s.card = n` and `hk : k ≤ n`, prove that
`(Finset.powersetCard (n - k) s).card = Nat.choose n k`.

Strategy:
1. Convert the powersetCard cardinality to `Nat.choose` (Level 17 pattern)
2. Substitute `s.card` with `n`
3. Apply `Nat.choose_symm hk` via rewriting
"

/-- The (n-k)-element subsets of an n-element set number choose(n, k). -/
Statement (n k : ℕ) (s : Finset ℕ) (hs : s.card = n) (hk : k ≤ n) :
    (Finset.powersetCard (n - k) s).card = Nat.choose n k := by
  Hint "Start by converting the powersetCard cardinality to a binomial
  coefficient using `Finset.card_powersetCard`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard]`."
  rw [Finset.card_powersetCard]
  Hint "Now substitute `s.card` with `n` using `hs`."
  Hint (hidden := true) "Try `rw [hs]`."
  rw [hs]
  Hint "The goal is `Nat.choose n (n - k) = Nat.choose n k`. The
  symmetry identity `Nat.choose_symm` says `choose n (n - k) = choose n k`
  when `k ≤ n`. Rewrite with it, passing the proof `hk`."
  Hint (hidden := true) "Try `rw [Nat.choose_symm hk]`."
  rw [Nat.choose_symm hk]

Conclusion "
Three steps: `card_powersetCard`, `rw [hs]`, `rw [choose_symm hk]`.

**The new pattern**: `rw [Nat.choose_symm hk]` passes a **proof
argument** inside the rewrite. The `hk : k <= n` is needed because
`choose_symm` requires evidence that the subtraction `n - k` is
well-defined (in natural numbers, subtraction truncates to 0).

**Why this matters for the boss**: The boss will use this exact
pattern — `rw [Nat.choose_symm ...]` with a proof argument — as
part of a larger proof. Practicing it here in isolation makes the
boss move familiar rather than surprising.

**Combinatorial meaning**: Choosing which $k$ elements to *include*
is the same as choosing which $n - k$ elements to *exclude*. So
$\\binom{n}{k} = \\binom{n}{n-k}$.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
