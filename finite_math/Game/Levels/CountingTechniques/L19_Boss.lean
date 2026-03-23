import Game.Metadata

World "CountingTechniques"
Level 19

Title "Boss: Counting Technique Integration"

Introduction "
# Boss: Four Techniques in One Proof

You've learned four major counting techniques:
1. **Injection/surjection bounds** — cardinality inequalities
2. **Sandwich equality** (`le_antisymm`) — equality from two bounds
3. **Double counting** (fiber decomposition) — `card_eq_sum_card_fiberwise`
4. **Averaging/bounding** (`sum_le_sum`) — bound sums term-by-term

This boss chains ALL four into one proof.

**The problem**: You have three finite types `alpha`, `beta`, `gamma` with:
- `f : alpha -> beta` is both injective and surjective (so `|alpha| = |beta|`)
- `g : beta -> gamma` partitions `beta` into fibers over `gamma`
- Each fiber of `g` has at most `k` elements
- But `|gamma| * k < |alpha|`

These conditions are contradictory. Prove `False` by:
1. **Injection bound** + **surjection bound** on `f` to get `|alpha| = |beta|`
2. **Fiber decomposition** of `g` to express `|beta|` as a sum of fiber sizes
3. **Sum bound** (`sum_le_sum`) to bound the fiber sum by `|gamma| * k`
4. Chain: `|alpha| = |beta| <= |gamma| * k < |alpha|` — contradiction!

No shortcuts — you must build the full chain.
"

/-- Injection + surjection + fiber decomposition + sum bound = contradiction. -/
Statement {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (f : α → β) (g : β → γ) (k : ℕ)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f)
    (hfib : ∀ c, (Finset.univ.filter (fun b => g b = c)).card ≤ k)
    (hlt : Fintype.card γ * k < Fintype.card α) :
    False := by
  -- Step 1: Injection bound
  Hint "Start with the injection bound: since `f` is injective,
  `|alpha| <= |beta|`."
  Hint (hidden := true) "Try:
  `have h_le := Fintype.card_le_of_injective f hinj`"
  have h_le := Fintype.card_le_of_injective f hinj
  -- Step 2: Surjection bound
  Hint "Now the surjection bound: since `f` is surjective,
  `|beta| <= |alpha|`."
  Hint (hidden := true) "Try:
  `have h_ge := Fintype.card_le_of_surjective f hsurj`"
  have h_ge := Fintype.card_le_of_surjective f hsurj
  -- Step 3: Sandwich equality
  Hint "Combine the two bounds with `le_antisymm` to get
  `|alpha| = |beta|`."
  Hint (hidden := true) "Try:
  `have heq := le_antisymm h_le h_ge`"
  have heq := le_antisymm h_le h_ge
  -- Step 4: Fiber decomposition
  Hint "Now decompose `|beta|` into fiber sizes using
  `card_eq_sum_card_fiberwise`. Every element of `beta` maps
  to some element of `gamma` via `g`, and `Finset.mem_univ`
  witnesses membership in `Finset.univ`."
  Hint (hidden := true) "Try:
  `have hmem : forall b in (Finset.univ : Finset beta), g b in (Finset.univ : Finset gamma) := fun _ _ => Finset.mem_univ _`
  then
  `have hsum := Finset.card_eq_sum_card_fiberwise hmem`"
  have hmem : ∀ b ∈ (Finset.univ : Finset β), g b ∈ (Finset.univ : Finset γ) :=
    fun _ _ => Finset.mem_univ _
  have hsum := Finset.card_eq_sum_card_fiberwise hmem
  Hint "Simplify `hsum`: the left side is `(Finset.univ).card`,
  which equals `Fintype.card beta`."
  Hint (hidden := true) "Try `rw [Finset.card_univ] at hsum`."
  rw [Finset.card_univ] at hsum
  -- Step 5: Sum bound
  Hint "Now bound the sum using `hfib`. Since each fiber has
  size at most `k`, use `Finset.sum_le_sum` to bound the
  sum of fiber sizes by the sum of `k`."
  Hint (hidden := true) "Try:
  `have hbound := Finset.sum_le_sum (fun (c : gamma) (_ : c in Finset.univ) => hfib c)`"
  have hbound := Finset.sum_le_sum (fun (c : γ) (_ : c ∈ Finset.univ) => hfib c)
  Hint "Simplify the right side: `sum c in univ, k` equals
  `|gamma| * k` via `sum_const` and `smul_eq_mul`."
  Hint (hidden := true) "Try:
  `rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound`"
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  -- Step 6: Contradiction
  Hint "Now `omega` sees the chain:
  `|alpha| = |beta| = sum sizes <= |gamma| * k < |alpha|`.
  That's a contradiction."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
Congratulations! You've completed the **Counting Techniques** world.

**The proof chain**:

| Step | Technique | Tool | Result |
|---|---|---|---|
| 1 | Injection bound | `card_le_of_injective` | `|alpha| <= |beta|` |
| 2 | Surjection bound | `card_le_of_surjective` | `|beta| <= |alpha|` |
| 3 | Sandwich equality | `le_antisymm` | `|alpha| = |beta|` |
| 4 | Fiber decomposition | `card_eq_sum_card_fiberwise` | `|beta| = sum of fiber sizes` |
| 5 | Sum bound | `sum_le_sum` + `sum_const` | `sum <= |gamma| * k` |
| 6 | Arithmetic | `omega` | `|alpha| <= |gamma| * k < |alpha|` is absurd |

This proof integrates ALL four counting techniques:
- **Injection/surjection bounds** establish `|alpha| = |beta|`
- **Fiber decomposition** expresses `|beta|` as a sum
- **Sum bounding** controls the sum
- **Arithmetic contradiction** closes the proof

**The four counting techniques in review**:

| Technique | When to use | Key theorem |
|---|---|---|
| Bijective counting | Prove `|A| = |B|` | `card_congr`, `le_antisymm` |
| Injection/surjection bounds | Prove `|A| <= |B|` or `|A| >= |B|` | `card_le_of_injective`, `card_le_of_surjective` |
| Strict inequality | Prove `|A| < |B|` | `card_lt_card` (subsets), injection + not surjective (functions) |
| Pigeonhole | Prove non-injectivity | `not_injective_of_card_lt`, `exists_ne_map_eq_of_card_lt` |
| Double counting | Decompose and bound counts | `card_eq_sum_card_fiberwise`, `sum_le_sum` |

These are the workhorses of combinatorial proofs. Nearly every
counting argument in discrete mathematics reduces to one of these
techniques, or — as in this boss — a combination of several.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
-- Force the full chain — no shortcuts
DisabledTheorem Fintype.card_of_bijective Fintype.card_congr Equiv.ofBijective Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
