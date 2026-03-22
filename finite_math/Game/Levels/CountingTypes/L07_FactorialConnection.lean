import Game.Metadata

World "CountingTypes"
Level 7

Title "The Factorial Connection"

Introduction "
# Connecting Falling Factorials to Factorials

In Level 6 you computed $3^{\\underline{3}} = 6$ by unfolding the
recursive definition. That value, 6, is also $3!$ (3 factorial).
This is no coincidence — when you select ALL items ($k = n$), the
falling factorial equals the ordinary factorial:

$$n^{\\underline{n}} = n!$$

Lean provides `Nat.factorial`:
- `Nat.factorial 0 = 1`
- `Nat.factorial (n + 1) = (n + 1) * Nat.factorial n`

And the connection theorem `Nat.descFactorial_self`:
```
Nat.descFactorial_self (n : ℕ) : n.descFactorial n = n.factorial
```

Why does this matter? The factorial appears throughout combinatorics:
- Permutations of $n$ items: $n!$
- Binomial coefficients: $\\binom{n}{k} = \\frac{n!}{k!(n-k)!}$
- Many identities factor through factorials

**Your task**: Prove that $n^{\\underline{n}} = n!$ for $n = 4$, using
`descFactorial_self`. First substitute the concrete value, then apply
the factorial connection.
"

/-- The falling factorial n^(n) equals n! -/
Statement (n : ℕ) (hn : n = 4) : n.descFactorial n = n.factorial := by
  Hint "Replace `n` with its concrete value first."
  Hint (hidden := true) "Try `rw [hn]`."
  rw [hn]
  Hint "Now use the factorial connection: `descFactorial_self` converts
  the falling factorial directly to the factorial."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_self]`."
  rw [Nat.descFactorial_self]

Conclusion "
$$n^{\\underline{n}} = n!$$

The theorem `Nat.descFactorial_self` captures this identity directly.
In Level 6, you proved $3^{\\underline{3}} = 6 = 3!$ by manual
unfolding — now you have the general shortcut.

This connects two counting perspectives:

| Notation | Meaning | Lean |
|---|---|---|
| $n^{\\underline{k}}$ | ordered selections of $k$ from $n$ | `Nat.descFactorial` |
| $n!$ | orderings of all $n$ items | `Nat.factorial` |
| $n^{\\underline{n}} = n!$ | selecting all = ordering all | `Nat.descFactorial_self` |

**Looking ahead**: The binomial coefficient $\\binom{n}{k}$ divides
the falling factorial by $k!$ to remove the ordering:
$\\binom{n}{k} = n^{\\underline{k}} / k!$. Having both `descFactorial`
and `factorial` as formal objects makes this definition precise.
"

/-- `Nat.descFactorial_self` states that `n.descFactorial n = n.factorial`.

When selecting all items from `n`, the falling factorial equals the
ordinary factorial.

## Syntax
```
rw [Nat.descFactorial_self]
```

## When to use it
When the goal contains `n.descFactorial n` and you want to convert to
`n.factorial`, or vice versa.
-/
TheoremDoc Nat.descFactorial_self as "Nat.descFactorial_self" in "Fintype"

/-- `Nat.factorial n` computes the factorial of `n`:
- `Nat.factorial 0 = 1`
- `Nat.factorial (n + 1) = (n + 1) * Nat.factorial n`

The factorial counts the number of permutations (orderings) of `n` items.
-/
DefinitionDoc Nat.factorial as "Nat.factorial"

NewTheorem Nat.descFactorial_self
NewDefinition Nat.factorial

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf rfl
