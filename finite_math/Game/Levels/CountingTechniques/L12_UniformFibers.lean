import Game.Metadata

World "CountingTechniques"
Level 12

Title "Uniform Fibers: Multiplication Principle"

Introduction "
# Double Counting with Uniform Fibers

The fiber decomposition says $|s| = \\sum_{b \\in t} |\\text{fiber}(b)|$.
A powerful special case: if every fiber has the *same* size `k`, then:

$$|s| = |t| \\cdot k$$

The proof combines three tools you know:
1. `card_eq_sum_card_fiberwise` — decompose into fiber sum
2. `Finset.sum_congr rfl hfib` — rewrite each summand from
   `|fiber(b)|` to `k` using the uniformity hypothesis
3. `Finset.sum_const` + `smul_eq_mul` — simplify `∑ b ∈ t, k`
   to `t.card • k` to `t.card * k`

**Your task**: Given that every fiber of `f` over `t` has size `k`,
prove that `s.card = t.card * k`.
"

/-- If every fiber has size k, then |s| = |t| * k. -/
Statement (s : Finset ℕ) (t : Finset ℕ) (f : ℕ → ℕ) (k : ℕ)
    (hf : ∀ x ∈ s, f x ∈ t)
    (hfib : ∀ b ∈ t, (s.filter (fun a => f a = b)).card = k) :
    s.card = t.card * k := by
  Hint "Start with the fiber decomposition: `card_eq_sum_card_fiberwise`
  gives you `s.card = ∑ b ∈ t, (fiber b).card`."
  Hint (hidden := true) "Try:
  `have h := Finset.card_eq_sum_card_fiberwise hf`"
  have h := Finset.card_eq_sum_card_fiberwise hf
  Hint "Now rewrite to use `h`, then simplify the sum.
  Since every fiber has size `k`, use `sum_congr rfl hfib`
  to replace each `|fiber(b)|` with `k`."
  Hint (hidden := true) "Try:
  `rw [h, Finset.sum_congr rfl hfib]`"
  rw [h, Finset.sum_congr rfl hfib]
  Hint "The goal is `∑ b ∈ t, k = t.card * k`.
  A constant sum `∑ b ∈ t, k` equals `t.card • k`
  by `Finset.sum_const`. Then `smul_eq_mul` converts `•` to `*`."
  Hint (hidden := true) "Try:
  `rw [Finset.sum_const, smul_eq_mul]`"
  rw [Finset.sum_const, smul_eq_mul]

Conclusion "
The uniform fiber multiplication principle:
1. `card_eq_sum_card_fiberwise hf` — decompose `|s|` into fiber sum
2. `sum_congr rfl hfib` — replace each fiber size with `k`
3. `sum_const` + `smul_eq_mul` — constant sum = count * value

**In plain mathematics**: This is the **rule of product** (or
multiplication principle): if a set can be decomposed into groups
of equal size, then the total count equals the number of groups
times the group size.

**Classic example**: A deck of cards has 4 suits, each with 13
cards. Total = $4 \\times 13 = 52$.

**Connection to `card_product`**: The multiplication principle
for Cartesian products (`card_product : |s \\times t| = |s| \\cdot |t|`)
is a special case. In `s \\times t`, the fiber of `b \\in t` under
projection `\\pi_2` is $s \\times \\{b\\}$, which has size $|s|$.
So $|s \\times t| = \\sum_{b \\in t} |s| = |t| \\cdot |s|$.
"

/-- `smul_eq_mul` converts scalar multiplication `n • m` to
ordinary multiplication `n * m` for natural numbers.

## Syntax
```
rw [smul_eq_mul]
```

## When to use it
When `Finset.sum_const` produces `s.card • c` and you want
`s.card * c`. The `•` (smul) notation means 'add `c` to itself
`n` times' which for natural numbers is just multiplication.
-/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Algebra"

NewTheorem smul_eq_mul

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
