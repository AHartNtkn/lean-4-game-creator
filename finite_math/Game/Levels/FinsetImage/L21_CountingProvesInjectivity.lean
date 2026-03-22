import Game.Metadata

World "FinsetImage"
Level 21

Title "Counting Proves Injectivity"

Introduction "
# The Payoff: Cardinality as a Proof Technique

Level 17 gave you `Finset.card_image_iff`:

$$|f(S)| = |S| \\iff f \\text{ is injective on } S$$

Now you'll use this as a **proof tool**. Consider
$f(n) = n \\cdot n + 1$ on $S = \\{0, 1, 2\\}$:

| $n$ | $f(n) = n^2 + 1$ |
|---|---|
| 0 | 1 |
| 1 | 2 |
| 2 | 5 |

The image $\\{1, 2, 5\\}$ has 3 elements, the same as $S$. By
`card_image_iff`, this means $f$ is injective on $S$.

Proving injectivity directly for a quadratic function requires
checking that $a^2 + 1 = b^2 + 1$ implies $a = b$ for all pairs
in $S$ — tedious. But counting the image is immediate: same
size means no collisions.

**Your task**: Prove that $f$ is injective on $S$ by converting
the goal to a cardinality equation, then letting Lean verify
the computation.

**The `←` modifier**: The `←` arrow before a theorem name tells `rw`
to apply the theorem **right-to-left** instead of left-to-right.
`Finset.card_image_iff` says `card = card ↔ InjOn`. Normally `rw`
would replace `card = card` with `InjOn`. With `←`, it replaces
`InjOn` with `card = card` — exactly what we want here.

Strategy:
1. `rw [← Finset.card_image_iff]` — convert the injectivity
   goal into a cardinality equation
2. `native_decide` — let Lean compute both sides and verify equality
"

/-- Counting proves injectivity: n ↦ n² + 1 is injective on {0, 1, 2}. -/
Statement :
    Set.InjOn (fun n : ℕ => n * n + 1) ↑({0, 1, 2} : Finset ℕ) := by
  Hint "Convert the injectivity goal into a cardinality equation.
  Use `rw [← Finset.card_image_iff]` — the `←` rewrites the goal
  from `Set.InjOn ...` to `(s.image f).card = s.card`."
  rw [← Finset.card_image_iff]
  Hint "The goal is now a concrete cardinality equation. Lean can
  compute both sides: the image is `(1, 2, 5)` with 3 elements,
  and the input has 3 elements. Use `native_decide` to let Lean
  verify this computationally."
  Hint (hidden := true) "Try `native_decide`."
  native_decide

Conclusion "
You just proved injectivity **without checking a single pair**.
Instead of showing $a^2 + 1 = b^2 + 1 \\implies a = b$ for all
$a, b \\in \\{0, 1, 2\\}$, you showed $|f(S)| = |S|$ and let
`card_image_iff` do the rest.

This is the counting-proves-injectivity technique:
1. `rw [← Finset.card_image_iff]` — convert to cardinality
2. `native_decide` (or `decide`) — verify computationally

The technique works whenever the domain is a concrete finset.
For abstract finsets, you'd need to compute or bound the
cardinality by other means.

This is the **payoff** of the cardinality arc (Levels 12-18):
cardinality isn't just a number — it's a proof technique. Knowing
$|f(S)| = |S|$ tells you the function has no collisions, which is
the *definition* of injectivity.

**Name this strategy**: 'counting proves injectivity.' It appears
throughout combinatorics — whenever you can count the image and
confirm no elements were lost, you've proved injectivity without
examining a single pair. The pattern is always the same:
1. `rw [← Finset.card_image_iff]` — convert to cardinality
2. Compute or bound the image size
3. Conclude injectivity

**The full circle**: You now have the complete equivalence for finite
sets: a function is injective on $S$ if and only if it preserves
cardinality ($|f(S)| = |S|$). Level 15 proved the forward direction
(`card_image_of_injective`: injective implies card preserved), Level 17
gave the biconditional (`card_image_iff`), and this level used the
reverse direction as a proof technique. For finite sets, counting IS
a proof of injectivity.

Next: a practice level for the `show` tactic applied to injectivity
proofs, then the boss.
"

NewTactic native_decide

-- Note: native_decide is intentionally enabled for this level
-- (not in DisabledTactic) since the level teaches computational verification.
DisabledTactic trivial «decide» simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
