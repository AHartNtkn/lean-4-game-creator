import Game.Metadata

World "BinomialCoefficients"
Level 15

Title "The Hockey Stick Identity"

Introduction "
# The Hockey Stick Identity

Look at a diagonal of Pascal's triangle and sum its entries:

$$\\binom{0}{k} + \\binom{1}{k} + \\binom{2}{k} + \\cdots + \\binom{n}{k} = \\binom{n+1}{k+1}$$

This is the **hockey stick identity** (also called the Christmas stocking
identity), because if you highlight the summed entries and the result in
Pascal's triangle, the shape looks like a hockey stick.

For example, with $k = 1$:
$$\\binom{0}{1} + \\binom{1}{1} + \\binom{2}{1} + \\binom{3}{1} = 0 + 1 + 2 + 3 = 6 = \\binom{4}{2}$$

This generalizes the Gauss sum formula from Level 14:
the sum $0 + 1 + 2 + \\cdots + n = \\binom{n+1}{2}$ is the hockey stick
with $k = 1$.

**Proof strategy**: Induction on $n$.
- **Base case** ($n = 0$): The sum has one term, $\\binom{0}{k}$. Show this
  equals $\\binom{1}{k+1}$ using the single-term sum pattern from Level 13.
- **Inductive step**: Peel off the last term with `sum_range_succ`,
  substitute the IH, then fold back using Pascal's identity in reverse.
"

/-- The hockey stick identity:
∑ i in range (n+1), choose i k = choose (n+1) (k+1). -/
Statement (n k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Nat.choose i k = Nat.choose (n + 1) (k + 1) := by
  Hint "Use **induction** on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case** (n = 0): The goal is
    `∑ i in range 1, choose i k = choose 1 (k + 1)`.

    First, simplify the sum. A sum over `range 1` has one term (at $i = 0$).
    Use `sum_range_succ` to peel it, then `sum_range_zero` to clear the
    empty sum."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]`."
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    Hint "The goal is `Nat.choose 0 k = Nat.choose 1 (k + 1)`.

    Expand the right side with Pascal's identity: `choose 1 (k+1) =
    choose 0 k + choose 0 (k+1)`. Then show `choose 0 (k+1) = 0`
    (you cannot choose $k+1$ items from $0$)."
    Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]` to expand the right side."
    rw [Nat.choose_succ_succ]
    Hint "The goal is `Nat.choose 0 k = Nat.choose 0 k + Nat.choose 0 (k + 1)`.

    Show that `choose 0 (k+1) = 0` using `choose_eq_zero_of_lt`
    (since $0 < k + 1$), then simplify with `add_zero`."
    Hint (hidden := true) "Try:
    `have h : Nat.choose 0 (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)`
    `rw [h, add_zero]`"
    have h : Nat.choose 0 (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h, add_zero]
  | succ n ih =>
    Hint "**Inductive step**: The goal is
    `∑ i in range (n + 2), choose i k = choose (n + 2) (k + 1)`.

    Strategy:
    1. Peel off the last term with `sum_range_succ`
    2. Substitute the IH
    3. Fold back using Pascal's identity in reverse (`← choose_succ_succ`)

    After peeling, the sum becomes `(∑ over range (n+1)) + choose (n+1) k`.
    The IH rewrites the sum to `choose (n+1) (k+1)`.
    Then `choose (n+1) k + choose (n+1) (k+1)` is exactly Pascal's
    identity for `choose (n+2) (k+1)`, read backward."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ]`."
    rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ]

Conclusion "
You proved the **hockey stick identity**:
$$\\sum_{i=0}^{n} \\binom{i}{k} = \\binom{n+1}{k+1}$$

**Skills integrated in this proof**:
1. `induction n with` — natural number induction
2. `Finset.sum_range_succ` — peeling off the last term (BigOpAlgebra)
3. `Finset.sum_range_zero` — empty sum equals 0 (SummationFormulas)
4. `Nat.choose_succ_succ` — Pascal's identity (Level 3)
5. `← rw` — backward rewrite (Level 7)
6. `Nat.choose_eq_zero_of_lt` — beyond the edge (Level 8)

**The key insight**: The inductive step uses **Pascal's identity in reverse**.
After peeling and substituting the IH, we have `choose(n+1, k) + choose(n+1, k+1)`,
which is exactly the Pascal expansion of `choose(n+2, k+1)`. The backward
rewrite `← choose_succ_succ` folds it back.

The base case uses the **collect-and-close** pattern (from FinsetInduction):
bring `choose 0 (k+1) = 0` into context with `have`, then close with a
rewrite. This is the same strategy you'll use whenever a goal has
structural facts that need to be made explicit before the arithmetic
resolves.

**Why \"hockey stick\"?** In Pascal's triangle, if you highlight a diagonal
sequence of entries and the entry just below the last one (on the opposite
side), the shape looks like a hockey stick:
```
    1
   1 1
  1 [2] 1
 1  3 [3] 1
1  4  6 [4]  1
1 5 10 10 [5]  1
       [20]
```
The bracketed entries show $\\binom{2}{2} + \\binom{3}{2} + \\binom{4}{2} + \\binom{5}{2} = 1 + 3 + 6 + 10 = 20 = \\binom{6}{3}$. The vertical
sequence is the \"stick\" and the bottom entry is the \"blade.\"
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
