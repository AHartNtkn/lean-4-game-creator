import Game.Metadata

World "Powerset"
Level 25

Title "Counting 2-Element Subsets"

Introduction "
# Concrete Counting with PowersetCard

A 5-element set has $\\binom{5}{2} = 10$ two-element subsets. Let's
prove this formally.

**Your task**: Given `hs : s.card = 5`, prove that
`(powersetCard 2 s).card = 10`.

You'll need:
- `card_powersetCard` to convert to `Nat.choose`
- `hs` to substitute the card value
- The fact that `Nat.choose 5 2 = 10` (which Lean computes automatically)
"

/-- A 5-element set has 10 two-element subsets. -/
Statement (s : Finset ℕ) (hs : s.card = 5) :
    (Finset.powersetCard 2 s).card = 10 := by
  Hint "Use `have` to bring `card_powersetCard` into the context."
  Hint (hidden := true) "Try `have h := Finset.card_powersetCard 2 s`."
  have h := Finset.card_powersetCard 2 s
  Hint "Now `h : (powersetCard 2 s).card = Nat.choose s.card 2`.
  Substitute the card of `s` using `hs`."
  Hint (hidden := true) "Try `rw [hs] at h`."
  rw [hs] at h
  Hint "Now `h` says the count equals `Nat.choose 5 2`, which
  Lean reduces to `10`. The hypothesis matches the goal."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
Three steps: `have h := card_powersetCard 2 s`, `rw [hs] at h`, `exact h`.

This is the same `have` + `rw at h` + `exact h` pattern from
Level 12 (counting all subsets). This pattern has appeared three
times now (Levels 12, 13, and this level). Let's name it:

**The instantiate-and-rewrite pattern**:
1. `have h := structure_lemma args` — bring a general identity
   into the context as a concrete hypothesis
2. `rw [known_value] at h` — specialize it using known data
3. `exact h` — close the goal with the specialized hypothesis

Use this pattern whenever the structure lemma does not directly
match the goal (because the goal has concrete values while the
lemma is stated generally). It is the workhorse for computing
specific counts from general formulas.

**Sanity check**: $\\binom{5}{2} = \\frac{5!}{2! \\cdot 3!} = \\frac{120}{2 \\cdot 6} = 10$. ✓

The boss uses this pattern but also applies identities from the
BinomialCoefficients world.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
