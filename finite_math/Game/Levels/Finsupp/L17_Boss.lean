import Game.Metadata

World "Finsupp"
Level 17

Title "Boss: Finitely Supported Functions"

Introduction "
# Boss: Putting It All Together

You have learned to construct finitely supported functions, evaluate
them at and away from the support point, reason about support, add
them pointwise, combine singles algebraically, and bound the support
of a sum.

Now put it all together. Prove five things:

1. **Support membership**: `5` belongs to the support of the
   three-term sum `single 5 3 + single 8 1 + single 5 4`.
2. **Evaluation**: The sum evaluates to `1` at position `8`.
3. **Support of a single**: The support of `single 5 7` is
   the singleton containing `5`.
4. **Algebraic combination**: Two singles at position `8` combine
   to give a singleton support.
5. **Support bound**: An element in the support of a sum is in the
   union of the individual supports.

Each part exercises a different combination of skills.
"

/-- Prove support membership, evaluation, support computation, algebraic combination, and support bound. -/
Statement :
    5 ∈ (Finsupp.single 5 3 + Finsupp.single 8 1 + Finsupp.single 5 4 : ℕ →₀ ℕ).support
    ∧ (Finsupp.single 5 3 + Finsupp.single 8 1 + Finsupp.single 5 4 : ℕ →₀ ℕ) 8 = 1
    ∧ (Finsupp.single 5 7 : ℕ →₀ ℕ).support = {5}
    ∧ (Finsupp.single 8 1 + Finsupp.single 8 6 : ℕ →₀ ℕ).support = {8}
    ∧ ∀ x ∈ (Finsupp.single 5 3 + Finsupp.single 8 1 + Finsupp.single 5 4 : ℕ →₀ ℕ).support,
        x ∈ (Finsupp.single 5 3 + Finsupp.single 8 1 : ℕ →₀ ℕ).support ∪ (Finsupp.single 5 4 : ℕ →₀ ℕ).support := by
  Hint "Split the conjunction into parts with `constructor`."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Part 1: support membership
  Hint "**Part 1**: Prove `5` is in the support. Convert support
  membership to a statement about the function value."
  Hint (hidden := true) "Try `rw [Finsupp.mem_support_iff]`."
  · rw [Finsupp.mem_support_iff]
    Hint "The goal is now about evaluating the sum at `5`. Decompose
    the outermost addition with `add_apply`."
    Hint (hidden := true) "Try `rw [Finsupp.add_apply]`."
    rw [Finsupp.add_apply]
    Hint "Decompose the inner addition too."
    Hint (hidden := true) "Try `rw [Finsupp.add_apply]`."
    rw [Finsupp.add_apply]
    Hint "Now evaluate each single at position `5`. The first one,
    `Finsupp.single 5 3`, has support point `5` — a match."
    Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
    rw [Finsupp.single_eq_same]
    Hint "The second single, `Finsupp.single 8 1`, has support point
    `8`, not `5`. Establish the inequality."
    Hint (hidden := true) "Try `have h : 5 ≠ 8 := by omega` then
    `rw [Finsupp.single_eq_of_ne h]`."
    have h : 5 ≠ 8 := by omega
    rw [Finsupp.single_eq_of_ne h]
    Hint "The third single, `Finsupp.single 5 4`, has support point
    `5` — another match. Values accumulate."
    Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
    rw [Finsupp.single_eq_same]
    Hint "The goal is now a concrete arithmetic inequality."
    Hint (hidden := true) "Try `omega`."
    omega
  -- Parts 2-5
  · Hint "Split the remaining conjunction."
    Hint (hidden := true) "Try `constructor`."
    constructor
    -- Part 2: evaluation at position 8
    · Hint "**Part 2**: Evaluate the sum at position `8`. Decompose."
      Hint (hidden := true) "Try `rw [Finsupp.add_apply]`."
      rw [Finsupp.add_apply]
      Hint (hidden := true) "Try `rw [Finsupp.add_apply]`."
      rw [Finsupp.add_apply]
      Hint "Now evaluate each single at position `8`. The first one,
      `Finsupp.single 5 3`, has support point `5`, not `8`."
      Hint (hidden := true) "Try `have h : 8 ≠ 5 := by omega` then
      `rw [Finsupp.single_eq_of_ne h]`."
      have h : 8 ≠ 5 := by omega
      rw [Finsupp.single_eq_of_ne h]
      Hint "The middle single, `Finsupp.single 8 1`, has support
      point `8` — a match."
      Hint (hidden := true) "Try `rw [Finsupp.single_eq_same]`."
      rw [Finsupp.single_eq_same]
      Hint "The third single also has support point `5`, not `8`.
      You can reuse the same inequality proof `h`."
      Hint (hidden := true) "Try `rw [Finsupp.single_eq_of_ne h]`."
      rw [Finsupp.single_eq_of_ne h]
      Hint (hidden := true) "Try `omega`."
      omega
    -- Parts 3-5
    · Hint "Split the remaining conjunction."
      Hint (hidden := true) "Try `constructor`."
      constructor
      -- Part 3: support of a single
      · Hint "**Part 3**: The support of `single 5 7` is the singleton
        containing `5`. Use `support_single_ne_zero`."
        Hint (hidden := true) "Try `apply Finsupp.support_single_ne_zero`.
        This leaves the goal `7 ≠ 0`."
        apply Finsupp.support_single_ne_zero
        Hint (hidden := true) "Try `omega`."
        omega
      -- Parts 4-5
      · Hint "Split the remaining conjunction."
        Hint (hidden := true) "Try `constructor`."
        constructor
        -- Part 4: algebraic combination + support
        · Hint "**Part 4**: Two singles at position `8` — combine them
          algebraically first, then compute the support of the result."
          Hint (hidden := true) "Try `rw [← Finsupp.single_add]` to
          combine `single 8 1 + single 8 6` into `single 8 7`."
          rw [← Finsupp.single_add]
          Hint "Now the goal is `(Finsupp.single 8 7).support = ...`.
          Use `support_single_ne_zero`."
          Hint (hidden := true) "Try `apply Finsupp.support_single_ne_zero`.
          This leaves the goal `7 ≠ 0`."
          apply Finsupp.support_single_ne_zero
          Hint (hidden := true) "Try `omega`."
          omega
        -- Part 5: support_add
        · Hint "**Part 5**: Show that any element in the support of
          the three-term sum is in the union of `(single 5 3 + single 8 1).support`
          and `(single 5 4).support`. This is `Finsupp.support_add`."
          Hint (hidden := true) "Try `intro x hx` to introduce the
          element and its membership proof."
          intro x hx
          Hint "Now apply `Finsupp.support_add` to the membership proof."
          Hint (hidden := true) "Try `exact Finsupp.support_add hx`."
          exact Finsupp.support_add hx

Conclusion "
You integrated all the Finsupp skills in a single proof:

**Part 1 — Support membership via evaluation**:
`mem_support_iff` converted support membership to a nonzero-ness
claim, then you evaluated the 3-term sum using `add_apply` twice
(for the nested addition), `single_eq_same` (for matching support
points), and `single_eq_of_ne` (for non-matching ones). Support
reasoning required evaluation, which required decomposition —
genuine skill integration.

**Part 2 — Evaluation at a different point**:
The same evaluation strategy at position `8` instead of `5` required
picking the *opposite* lemma at each step — `single_eq_of_ne` for
the singles at `5`, and `single_eq_same` for the single at `8`.

**Part 3 — Support of a single**:
A quick application of `support_single_ne_zero` — the lemma from
Level 3 that computes the support when the value is nonzero.

**Part 4 — Algebraic combination**:
`← single_add` combined two singles at the same position into one,
then `support_single_ne_zero` computed the support of the result.
This is the algebraic approach: simplify first, then reason about
the simpler expression.

**Part 5 — Support bound**:
`support_add` shows that the support of a sum is contained in the
union of the supports. This is the ⊆ direction from Level 14 —
an element in `(f + g).support` must be in `f.support ∪ g.support`.

The **finsupp evaluation strategy** — `add_apply` →
`single_eq_same`/`single_eq_of_ne` → arithmetic — is the fundamental
technique for computing with finitely supported functions.

**Connection to big operators**: Every finitely supported function can
be decomposed as a sum of singles: `f = f.sum Finsupp.single`. The
operation `Finsupp.sum` is actually `Finset.sum` over the support —
connecting directly to the big operator machinery from earlier worlds.
This is why finitely supported functions are the algebraic backbone
of formal sums, polynomials, and free modules.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
