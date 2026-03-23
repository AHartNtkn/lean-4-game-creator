import Game.Metadata

World "CountingTechniques"
Level 11

Title "Double Counting: Fiber Decomposition"

Introduction "
# Technique 4: Double Counting

**Double counting** computes the same quantity two different ways
and sets the results equal. The most common form decomposes a
set into **fibers** — groups of elements that share the same
image under a function.

Given a function `f` mapping `s` into `t`, the **fiber** of
`b ∈ t` is the set of all `a ∈ s` with `f a = b`:

$$\\text{fiber}(b) = \\{a \\in s \\mid f(a) = b\\}$$

The fiber decomposition principle says:

$$|s| = \\sum_{b \\in t} |\\text{fiber}(b)|$$

In Lean, this is `Finset.card_eq_sum_card_fiberwise`:

```
Finset.card_eq_sum_card_fiberwise :
  (∀ x ∈ s, f x ∈ t) →
  s.card = ∑ b ∈ t, (s.filter (f · = b)).card
```

The fibers partition `s`, so their sizes add up to `|s|`.

**Your task**: Given that `f` maps `s` into `t` and `s` has
20 elements, prove the fiber sum also equals 20.
"

/-- The fiber decomposition gives: sum of fiber sizes = |s|. -/
Statement (s : Finset ℕ) (t : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ x ∈ s, f x ∈ t)
    (hs : s.card = 20) :
    ∑ b ∈ t, (s.filter (fun a => f a = b)).card = 20 := by
  Hint "Apply `Finset.card_eq_sum_card_fiberwise` to get the
  equation `s.card = ∑ b ∈ t, (filter ...).card`. This decomposes
  the set into fibers."
  Hint (hidden := true) "Try:
  `have h := Finset.card_eq_sum_card_fiberwise hf`"
  have h := Finset.card_eq_sum_card_fiberwise hf
  Hint "Now you have `h : s.card = ∑ ...` and `hs : s.card = 20`.
  The goal `∑ ... = 20` follows by combining these two facts."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The fiber decomposition applied:
1. `have h := Finset.card_eq_sum_card_fiberwise hf` — decompose
   `|s|` into a sum over fibers
2. `omega` — combine `h : s.card = ∑ ...` and `hs : s.card = 20`

**Why this matters**: The fiber decomposition is the formal
foundation of double counting. Instead of counting `s` directly,
you organize its elements by which target they map to and sum
the group sizes. The total can't change — it's the same set
counted a different way.

**In plain mathematics**: If `f : S \\to T` and every element of
`S` maps to some element of `T`, then:

$$|S| = \\sum_{b \\in T} |f^{-1}(b)|$$

where $f^{-1}(b) = \\{a \\in S : f(a) = b\\}$ is the preimage (fiber)
of $b$.

**Connection to inclusion-exclusion**: Fiber decomposition and
inclusion-exclusion (from the Cardinality world) are both forms
of double counting. Fiber decomposition partitions a set by
function values and sums the parts. Inclusion-exclusion corrects
for overlapping subsets: `|A union B| = |A| + |B| - |A cap B|`.
Both count the same set two different ways — fibers organize
by a function, I-E organizes by overlapping membership.

**Connection to counting**: If every fiber has the same size `k`,
then $|S| = |T| \\cdot k$. This is the multiplication principle —
next level!
"

/-- `Finset.card_eq_sum_card_fiberwise hf` states that if
`hf : ∀ x ∈ s, f x ∈ t` (f maps s into t), then
`s.card = ∑ b ∈ t, (s.filter (f · = b)).card`.

## Syntax
```
have h := Finset.card_eq_sum_card_fiberwise hf
```

## When to use it
When you want to decompose a set's cardinality into a sum over
fibers. This is the formal version of double counting: 'count
the same set two different ways.'

## Example
If `f` assigns colors to elements, then the total count equals
the sum of elements of each color.
-/
TheoremDoc Finset.card_eq_sum_card_fiberwise as "Finset.card_eq_sum_card_fiberwise" in "Card"

NewTheorem Finset.card_eq_sum_card_fiberwise

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
