import Game.Metadata

World "SurjectiveWorld"
Level 5

Title "Structural Surjectivity: Projection"

TheoremTab "Function"

Introduction "
# A Non-Arithmetic Example

Every surjectivity proof so far used arithmetic functions and `omega` for
verification. But surjectivity is not fundamentally about arithmetic — it
is about covering the codomain.

**Projection**: `Prod.fst : ℕ × ℕ → ℕ` maps a pair to its first
component: `Prod.fst (a, b) = a`.

**Claim**: `Prod.fst` is surjective.

The witness for any `a : ℕ` is the pair `(a, 0)` — the second component
can be anything. The verification is `Prod.fst (a, 0) = a`, which is true
by **definition** — no `omega` needed!

**The takeaway**: Surjectivity can arise from **structure** (projection
always hits the first component) rather than arithmetic calculation. Not
every witness verification requires `omega` — some are closed by `rfl`.
"

/-- The first projection from ℕ × ℕ to ℕ is surjective. -/
Statement : Function.Surjective (Prod.fst : ℕ × ℕ → ℕ) := by
  Hint "Start with `intro a` as always for a surjectivity proof."
  intro a
  Hint "You need a pair `p : ℕ × ℕ` with `Prod.fst p = a`. The pair
  `(a, 0)` works — its first component is `a`. Use `use (a, 0)`."
  Hint (hidden := true) "`use (a, 0)`."
  use (a, 0)

Conclusion "
A two-step proof! The witness `(a, 0)` is verified by definition — no
arithmetic needed.

**Compare verification methods**:

| Level | Function | Witness | Verification |
|---|---|---|---|
| Level 1 | `n ↦ n + 1` on ℤ | `b - 1` | `omega` |
| Level 4 | `n ↦ n / 2` on ℕ | `2 * b` | `omega` |
| This level | `Prod.fst` | `(a, 0)` | `rfl` (definitional) |

**Why this matters**: Surjectivity is about the existence of preimages,
not about how you verify them. Arithmetic functions need `omega`;
structural functions like projections are verified by unfolding definitions.
As proofs get more abstract (composition, right inverses), the witnesses
come from hypotheses rather than explicit construction, and verification
uses `exact` rather than `omega`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl Function.Surjective.comp Function.RightInverse.surjective Function.HasRightInverse.surjective Prod.fst_surjective
