import Game.Metadata

World "Products"
Level 10

Title "Sigma Recovers Product"

Introduction "
# When Sigma Reduces to Product

The previous level's conclusion claimed that when every fiber
has the same size, sigma cardinality recovers product cardinality.
Let's **prove** that claim.

If `t` is constant — every index gets the same finset — then
`card_sigma` gives $\\sum_{i \\in s} |t| = |s| \\cdot |t|$,
which is exactly `card_product`.

**Your task**: Prove that `(s.sigma (fun _ => t)).card = s.card * t.card`.

You'll need `Finset.card_sigma` to convert to a sum, then
`Finset.sum_const` to evaluate the constant sum. Recall that
`Finset.sum_const` gives `\\sum_{x \\in s} c = s.card \\bullet c`
where `\\bullet` is scalar multiplication.

**Heads up**: After applying `sum_const`, the goal will show
`s.card • t.card` using the `•` (nsmul) notation. Don't worry
— for natural numbers, scalar multiplication `•` is the same
as ordinary multiplication `*`. The goal will close with `rfl`
because Lean recognizes this definitional equality.
"

/-- When all fibers are the same, sigma cardinality equals product cardinality. -/
Statement (s : Finset ℕ) (t : Finset ℕ) :
    (s.sigma (fun _ => t)).card = s.card * t.card := by
  Hint "Convert the sigma cardinality to a sum using `Finset.card_sigma`."
  Hint (hidden := true) "Try `rw [Finset.card_sigma]`."
  rw [Finset.card_sigma]
  Hint "The sum is constant — every term is `t.card`.
  Use `Finset.sum_const` to simplify it."
  Hint (hidden := true) "Try `rw [Finset.sum_const]`.
  This gives `s.card * t.card = s.card * t.card` (for natural
  numbers, scalar multiplication is ordinary multiplication),
  which closes by `rfl`."
  rw [Finset.sum_const]
  Hint (hidden := true) "Try `rfl` — for natural numbers,
  scalar multiplication is ordinary multiplication."
  rfl

Conclusion "
You've proved that constant-fiber sigma is exactly product:

$$|s.\\text{sigma}\\ (\\lambda\\_.\\ t)| = \\sum_{i \\in s} |t| = |s| \\cdot |t| = |s \\times^s t|$$

This confirms that `Finset.product` is the special case of
`Finset.sigma` where the fiber doesn't depend on the index.
Sigma is the generalization; product is the uniform case.

This isn't just a cardinality coincidence — it reflects a
structural fact. The type `Σ _ : α, β` is isomorphic to
`α × β` (a dependent pair with a constant family is just an
ordinary pair). So `s.sigma (fun _ => t)` and `s ×ˢ t` have
the same elements, not just the same count.

**Connection to `sum_const`**: The identity
$\\sum_{i \\in s} c = |s| \\cdot c$ from the Big Operators world
is what bridges sigma cardinality to product cardinality.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
