import Game.Metadata

World "PascalsTriangle"
Level 2

Title "Symmetry in Action"

Introduction "
# Row Symmetry

Each row of Pascal's triangle reads the same forwards and backwards.
In row $n + 6$, the entries at positions $3$ and $n + 3$ are equal,
because $(n + 6) - 3 = n + 3$. These two positions are equidistant
from the edges of the row.

In Lean, `Nat.choose_symm` says:
```
Nat.choose_symm (h : k ≤ n) : Nat.choose n (n - k) = Nat.choose n k
```

**Your task**: Prove $\\binom{n+6}{3} = \\binom{n+6}{n+3}$ using symmetry.
Note that `choose_symm h` proves `choose n (n - k) = choose n k`.
Since $(n+6) - 3 = n + 3$, you need to flip the goal to match.
"

/-- C(n+6, 3) = C(n+6, n+3): symmetry of Pascal's triangle. -/
Statement (n : ℕ) : Nat.choose (n + 6) 3 = Nat.choose (n + 6) (n + 3) := by
  Hint "The symmetry lemma `Nat.choose_symm (h : k ≤ n)` proves
  `choose n (n - k) = choose n k`. With `n := n+6` and `k := 3`,
  it gives `choose (n+6) ((n+6) - 3) = choose (n+6) 3`, i.e.,
  `choose (n+6) (n+3) = choose (n+6) 3`.

  The goal has the equality in the other direction. Use `symm` first."
  Hint (hidden := true) "Try `symm` to flip the goal."
  symm
  Hint "The goal is now `Nat.choose (n + 6) (n + 3) = Nat.choose (n + 6) 3`.
  You need `h : 3 ≤ n + 6` for `choose_symm`."
  Hint (hidden := true) "Try `have h : 3 ≤ n + 6 := by omega`."
  have h : 3 ≤ n + 6 := by omega
  Hint "Now apply `choose_symm` with the inequality."
  Hint (hidden := true) "Try `exact Nat.choose_symm h`."
  exact Nat.choose_symm h

Conclusion "
$\\binom{n+6}{3} = \\binom{n+6}{n+3}$.

**The flip-apply pattern**: When using `choose_symm`:
1. `symm` — flip the goal to match the lemma's direction
2. `have h : k ≤ n := by omega` — establish the inequality
3. `exact Nat.choose_symm h` — apply the lemma

This is an instance of a general strategy you will see repeatedly:
**reshape-flip-apply**. When a known lemma almost matches the goal
but the form is slightly off, reshape the goal first, then flip
and apply. Here the 'reshape' was trivial (just `symm`), but in
later levels you will need an explicit rewrite step before flipping.
Watch for this pattern — it recurs throughout the world.

**Visual check**: In row $n + 6$, positions $3$ and $n + 3$ are
equidistant from the edges (both are 3 from their respective end).
Symmetry means these entries are always equal, regardless of $n$.

Symmetry means you only need to compute half the row: if you know
the entries at positions $0, 1, \\ldots, \\lfloor n/2 \\rfloor$, the
rest follow by symmetry.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith rfl
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
