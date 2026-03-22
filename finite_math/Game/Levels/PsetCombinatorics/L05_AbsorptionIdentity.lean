import Game.Metadata

World "PsetCombinatorics"
Level 5

Title "Absorption Through Powerset"

Introduction "
# The Absorption Identity via Subsets

In the BinomialCoefficients world (Level 10), you proved the
**absorption identity**:

$$(n + 1) \\cdot \\binom{n}{k} = (k + 1) \\cdot \\binom{n+1}{k+1}$$

with the **committee chair** double counting argument: both sides
count the number of committees with a designated chair.

Now apply it with a **powerset layer**: given a finset $s$ with
$|s| = n$, the number of $2$-element subsets is $\\binom{n}{2}$.
Prove:

$$(n + 1) \\cdot |\\text{powersetCard } 2\\ s| = 3 \\cdot \\binom{n+1}{3}$$

**Strategy**:
1. Strip the powerset layer with `Finset.card_powersetCard` and `hs`
2. Apply `Nat.add_one_mul_choose_eq` (absorption with $k = 2$)
3. Close with `ring`
"

/-- The absorption identity through powerset counting. -/
Statement (n : ℕ) (s : Finset ℕ) (hs : s.card = n) :
    (n + 1) * (Finset.powersetCard 2 s).card = 3 * Nat.choose (n + 1) 3 := by
  Hint "First, strip the powerset layer: convert
  `(powersetCard 2 s).card` to `choose n 2` using
  `Finset.card_powersetCard`, then substitute `s.card` with `n`."
  Hint (hidden := true) "Try `rw [Finset.card_powersetCard, hs]`."
  rw [Finset.card_powersetCard, hs]
  Hint "The goal is `(n + 1) * choose n 2 = 3 * choose (n + 1) 3`.

  The left side is an instance of the absorption identity
  `Nat.add_one_mul_choose_eq` with `k = 2`:
  `(n + 1) * choose n 2 = choose (n + 1) 3 * 3`.

  Apply it to rewrite the left side."
  Hint (hidden := true) "Try `rw [Nat.add_one_mul_choose_eq]`."
  rw [Nat.add_one_mul_choose_eq]
  Hint "The goal is `choose (n + 1) 3 * 3 = 3 * choose (n + 1) 3`.
  Close with `ring` (multiplication is commutative)."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
Another instance of **strip-and-apply**: strip with
`card_powersetCard`, then apply `add_one_mul_choose_eq`.

The formal proof delegates the double counting argument to
Mathlib's `add_one_mul_choose_eq`, which encapsulates it
algebraically. The combinatorial meaning: both sides count
(designated person, team of 2) triples from $n + 1$ people.

This technique — counting the same quantity in two different
ways — is called **double counting**. It will return as a formal
proof technique in the CountingTechniques world.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
