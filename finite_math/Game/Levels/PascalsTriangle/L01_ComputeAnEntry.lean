import Game.Metadata

World "PascalsTriangle"
Level 1

Title "Walking Down the Triangle"

Introduction "
# Pascal's Triangle, Row by Row

Welcome to Pascal's triangle — the most famous triangular array in
mathematics:
```
          1
         1 1
        1 2 1
       1 3 3 1
      1 4 6 4 1
     1 5 10 10 5 1
```

Each entry is a binomial coefficient $\\binom{n}{k}$, and each interior
entry is the sum of the two entries above it (Pascal's identity).

In the BinomialCoefficients world, you proved identities **about** the
entries. In this world, you will explore the **triangle itself** as a
geometric object: its rows, its diagonals, and a new construction —
the **antidiagonal** — that organizes pairs $(i, j)$ with $i + j = n$.

**Warm-up**: Show that expanding the second column of Pascal's triangle
two steps gives a recursive formula. The tools are the same as
BinomialCoefficients:
- `Nat.choose_succ_succ` to expand interior entries
- `Nat.choose_one_right` to simplify the edge entries
"

/-- Expanding C(n+4, 2) by walking down the triangle two steps. -/
Statement (n : ℕ) :
    Nat.choose (n + 4) 2 = n + 3 + (n + 2 + Nat.choose (n + 2) 2) := by
  Hint "Expand C(n+4, 2) using Pascal's identity:
  C(n+4, 2) = C(n+3, 1) + C(n+3, 2)."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]
  Hint "Good — simplify C(n+3, 1) = n+3 using `choose_one_right`."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right]`."
  rw [Nat.choose_one_right]
  Hint "Now expand C(n+3, 2) with Pascal's identity again."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]
  Hint "Simplify C(n+2, 1) = n+2."
  Hint (hidden := true) "Try `rw [Nat.choose_one_right]`."
  rw [Nat.choose_one_right]

Conclusion "
You expanded:
$$\\binom{n+4}{2} = (n+3) + (n+2) + \\binom{n+2}{2}$$

Each expansion peels off one edge entry (`choose_one_right`) and
leaves a smaller interior entry. This is the same recursive walk
through the triangle as in BinomialCoefficients — now with a
variable $n$ instead of fixed numbers.

**Pattern recap**: Expand with `choose_succ_succ`, simplify edges
with `choose_one_right`. Repeat until the remaining term is
small enough.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
