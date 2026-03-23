import Game.Metadata

World "SetWorld"
Level 8

Title "Compound Predicates"

Introduction "
# Compound Predicates

So far, each set predicate has tested a single condition. But predicates
can combine conditions using logical connectives.

The set `{n : ℕ | n < 10 ∧ Even n}` contains even numbers less than 10:
the set $\\{0, 2, 4, 6, 8\\}$.

Membership unfolds to the conjunction: `6 ∈ {n | n < 10 ∧ Even n}`
becomes `6 < 10 ∧ Even 6`. To prove a conjunction, you split it with
`constructor` and prove each part separately.

The proof strategy:
1. `constructor` — split `6 < 10 ∧ Even 6` into two goals
2. Prove `6 < 10` with `omega`
3. Prove `Even 6` by providing the witness `3` (since `6 = 3 + 3`)

**Your task**: Prove that 6 belongs to the set of even numbers less than 10.
"

/-- 6 belongs to the set of even naturals less than 10. -/
Statement : (6 : ℕ) ∈ {n : ℕ | n < 10 ∧ Even n} := by
  Hint "The membership unfolds to `6 < 10 ∧ Even 6` — a conjunction.
  Use `constructor` to split it into two goals."
  constructor
  · Hint "The goal is `6 < 10`. Use `omega`."
    omega
  · Hint "The goal is `Even 6`, which means `∃ r, 6 = r + r`.
    Provide the witness: `use 3`."
    Hint (hidden := true) "`use 3` substitutes `r = 3` and the
    remaining goal `6 = 3 + 3` is closed automatically."
    use 3

Conclusion "
You proved that 6 is both less than 10 AND even. The proof split
the conjunction with `constructor` and handled each part separately.

This illustrates a key principle: **compound set predicates reduce to
compound logical statements**. When a set is defined by `P ∧ Q`,
membership requires proving both `P` and `Q`.

| Set predicate | Membership requires |
|---|---|
| `P x` (simple) | Prove `P x` |
| `P x ∧ Q x` (conjunction) | Prove both — use `constructor` |
| `P x ∨ Q x` (disjunction) | Prove either — use `left` or `right` |
| `¬ P x` (negation) | Prove `P x → False` — use `intro` |

You will see these patterns again when you learn about set **intersection**
(which corresponds to `∧`) and **union** (which corresponds to `∨`).
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
