import Game.Metadata

World "CountingTechniques"
Level 13

Title "Bounding with Non-Uniform Fibers"

Introduction "
# From Uniform to Non-Uniform Fibers

Level 12 handled uniform fibers (every group has exactly `k` members).
But what if fibers have *different* sizes? You can still bound
the total using **`Finset.sum_le_sum`**:

```
Finset.sum_le_sum :
  (forall x in s, f x <= g x) ->
  sum x in s, f x <= sum x in s, g x
```

This says: if you bound each term of a sum, the total sum is
bounded too. Combined with `sum_const` and `smul_eq_mul`, this
lets you bound a fiber sum by `|t| * k` when each fiber has
at most `k` elements.

**Problem**: A club assigns members to 5 committees. Each committee
has at most 4 members. Prove the club has at most 20 members.

**Proof plan**:
1. Fiber decomposition: `|members| = sum of committee sizes`
2. Sum bound: each committee size <= 4, so `sum <= sum 4 = 5 * 4`
3. Therefore `|members| <= 20`
"

/-- If each of 5 committees has at most 4 members, the total is at most 20. -/
Statement (members : Finset ℕ) (committees : Finset ℕ) (assign : ℕ → ℕ)
    (hassign : ∀ x ∈ members, assign x ∈ committees)
    (hcomm : committees.card = 5)
    (hupper : ∀ c ∈ committees,
      (members.filter (fun m => assign m = c)).card ≤ 4) :
    members.card ≤ 20 := by
  Hint "Start with fiber decomposition to express
  `members.card` as a sum of committee sizes."
  Hint (hidden := true) "Try:
  `have h := Finset.card_eq_sum_card_fiberwise hassign`"
  have h := Finset.card_eq_sum_card_fiberwise hassign
  Hint "Now use `Finset.sum_le_sum` to bound the sum.
  Since each committee has at most 4 members (`hupper`),
  the sum of actual sizes is at most the sum of 4s."
  Hint (hidden := true) "Try:
  `have hbound := Finset.sum_le_sum hupper`"
  have hbound := Finset.sum_le_sum hupper
  Hint "The right side is `sum c in committees, 4`.
  Simplify to `committees.card * 4` using `sum_const`
  and `smul_eq_mul`, then substitute `hcomm`."
  Hint (hidden := true) "Try:
  `rw [Finset.sum_const, smul_eq_mul, hcomm] at hbound`"
  rw [Finset.sum_const, smul_eq_mul, hcomm] at hbound
  Hint "Now `h` says `members.card = sum ...` and `hbound`
  says `sum ... <= 20`. Combine with `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
Bounding with non-uniform fibers:
1. `card_eq_sum_card_fiberwise` — decompose into fiber sizes
2. `sum_le_sum hupper` — bound each term by the upper bound
3. `sum_const` + `smul_eq_mul` — constant sum = count * value
4. `omega` — combine the bound with the decomposition

**Uniform vs. non-uniform**:
- Level 12 (uniform): every fiber has size *exactly* `k`,
  so `|s| = |t| * k`
- This level (non-uniform): every fiber has size *at most* `k`,
  so `|s| <= |t| * k`

The non-uniform version is more common in practice. You rarely
know exact fiber sizes, but upper bounds are often available.

**Connection to the averaging argument**: If `|s| > |t| * k`,
then NOT every fiber can have size <= `k` — some fiber must be
larger. That's the pigeonhole principle viewed through the lens
of double counting. You'll prove this in Level 16.

**Connection to inclusion-exclusion**: Fiber decomposition and
inclusion-exclusion are both forms of 'double counting.' Fiber
decomposition partitions a set and sums the part sizes.
Inclusion-exclusion (from the Cardinality world) corrects for
overlaps: `|A union B| = |A| + |B| - |A intersect B|`. Both
count the same set two ways — fibers by function, I-E by
overlapping subsets.
"

/-- `Finset.sum_le_sum h` states that if `forall x in s, f x <= g x`,
then `sum x in s, f x <= sum x in s, g x`.

## Syntax
```
have hbound := Finset.sum_le_sum (fun x hx => h x hx)
```

## When to use it
When you need to bound a sum by replacing each term with a
larger (or equal) term. Often used with `sum_const` to compare
against a constant.
-/
TheoremDoc Finset.sum_le_sum as "Finset.sum_le_sum" in "BigOp"

NewTheorem Finset.sum_le_sum

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
