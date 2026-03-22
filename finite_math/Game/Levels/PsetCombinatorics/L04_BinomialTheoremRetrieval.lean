import Game.Metadata

World "PsetCombinatorics"
Level 4

Title "Binomial Theorem Retrieval"

Introduction "
# Recognize the Pattern

In BinomialTheorem, you learned to specialize `add_pow_nat`:

$$\\text{add\\_pow\\_nat}(x, y, n) : (x + y)^n = \\sum_{{m=0}}^{{n}} x^m \\cdot y^{{n-m}} \\cdot \\binom{{n}}{{m}}$$

Each choice of $x$ and $y$ produces a different identity.
Level 3 used $\\mathbb{Z}$ specialization ($x = -1, y = 3$).

Now try an $\\mathbb{N}$ specialization. Prove:

$$\\sum_{{m=0}}^{{n}} 3^m \\cdot 2^{{n-m}} \\cdot \\binom{{n}}{{m}} = 5^n$$

**Which values of $x$ and $y$ give this identity?**
"

/-- The binomial theorem specialized to x = 3, y = 2. -/
Statement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), 3 ^ m * 2 ^ (n - m) * Nat.choose n m = 5 ^ n := by
  Hint "The summand has the form $x^m \\cdot y^(n-m) \\cdot C(n, m)$.
  What are $x$ and $y$? They are $3$ and $2$, giving
  $(3 + 2)^n = 5^n$.

  Specialize `add_pow_nat` and close."
  Hint (hidden := true) "Try `have h := add_pow_nat 3 2 n` then `exact h.symm`."
  have h := add_pow_nat 3 2 n
  exact h.symm

Conclusion "
You recognized the binomial theorem pattern and chose the right
values: $x = 3, y = 2$ gives $(3 + 2)^n = 5^n$.

Every specialization of `add_pow_nat` produces a different
identity. The core retrieval skill: given a sum involving
$x^m \\cdot y^{{n-m}} \\cdot C(n,m)$, read off $x$ and $y$ from
the summand and specialize.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff Nat.choose_two_right
