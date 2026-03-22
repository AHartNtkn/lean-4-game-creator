import Game.Metadata

World "Finsupp"
Level 10

Title "The Algebraic Identity"

Introduction "
# From Values to Functions

In the last level you proved that `(single 4 (-3) + single 4 5) 4 = 2`
by evaluating pointwise with `ℤ` values. But there is a stronger fact:
the two singles at the same point **combine into a single** whose
value is the sum:

```
Finsupp.single_add :
  Finsupp.single a (b₁ + b₂) = Finsupp.single a b₁ + Finsupp.single a b₂
```

This is function equality, not just agreement at one point. The
left side is one single with value `b₁ + b₂`, and the right side
is the sum of two singles. They are the **same function**.

This is the algebraic form of accumulation. Where the previous
level showed that values add at a shared position, this lemma says
the entire functions are equal — a fact you can use to simplify
expressions algebraically.

**Your task**: Prove that `single 4 3 + single 4 5 = single 4 8`
using `Finsupp.single_add`. You will need a **backward rewrite**
`rw [← Finsupp.single_add]` to combine the two singles on the
left into a single whose value is `3 + 5`.
"

/-- Two singles at the same point combine into one. -/
Statement : Finsupp.single 4 3 + Finsupp.single 4 5 = Finsupp.single 4 (8 : ℕ) := by
  Hint "Use a backward rewrite to combine the left side. The lemma
  `Finsupp.single_add` says `single a (b₁ + b₂) = single a b₁ + single a b₂`.
  Rewriting backwards replaces `single a b₁ + single a b₂` with
  `single a (b₁ + b₂)`."
  Hint (hidden := true) "Try `rw [← Finsupp.single_add]`. This
  combines `single 4 3 + single 4 5` into `single 4 (3 + 5)`,
  which Lean recognizes as `single 4 8`."
  rw [← Finsupp.single_add]

Conclusion "
You have proved that `single 4 3 + single 4 5 = single 4 8` as
*function equality*, not just pointwise agreement. This is the
algebraic form of accumulation.

In polynomial language, you just proved that **3x⁴ + 5x⁴ = 8x⁴**:
the Finsupp `single 4 3` represents the monomial `3x⁴` (coefficient
`3` at degree `4`), and adding two monomials at the same degree
gives a monomial whose coefficient is the sum.

The backward rewrite `rw [← lemma]` is useful whenever you want to
*combine* rather than *expand*. Here, `← single_add` combined two
singles into one. The forward direction `rw [single_add]` would
expand one single into a sum of two.

**Pattern**: `rw [← Finsupp.single_add]` to combine
`single a b₁ + single a b₂` into `single a (b₁ + b₂)`.
"

TheoremTab "Finsupp"
NewTheorem Finsupp.single_add

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
