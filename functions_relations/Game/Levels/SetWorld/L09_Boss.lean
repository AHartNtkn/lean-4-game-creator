import Game.Metadata

World "SetWorld"
Level 9

Title "Boss: Sets are Predicates"

Introduction "
# Boss: Putting It All Together

Time to combine everything. You are given an abstract predicate `p`
on natural numbers, with two hypotheses:

- `hp : ∀ n, Even n → p n` — every even number satisfies `p`
- `hq : ∀ n, p n → Even n` — every number satisfying `p` is even

Together these say: `p` holds for exactly the even numbers.

You must prove two things:
1. `4 ∈ {n | p n}` — 4 is in the p-set (because 4 is even)
2. `3 ∉ {n | p n}` — 3 is NOT in the p-set (because 3 is odd)

This combines:
- Membership via hypothesis (Levels 1–2, 4): use `apply hp` then
  provide a witness for `Even 4`
- Non-membership via contradiction (Levels 3, 5): assume `p 3`,
  derive `Even 3` from `hq`, destructure the existential with
  `obtain`, then reach an arithmetic contradiction

Start with `constructor` to split the conjunction.
"

/-- Given hypotheses about a predicate p, prove membership and
non-membership in the set defined by p. -/
Statement (p : ℕ → Prop) (hp : ∀ n, Even n → p n) (hq : ∀ n, p n → Even n) :
    4 ∈ {n | p n} ∧ 3 ∉ {n | p n} := by
  Hint "The goal is a conjunction. Use `constructor` to split it
  into two parts."
  constructor
  -- Part 1: 4 ∈ {n | p n}, which reduces to p 4
  · Hint "The goal is `p 4`. You have `hp : ∀ n, Even n → p n`.
    Use `apply hp` to reduce the goal to `Even 4`."
    Hint (hidden := true) "`apply hp` matches the conclusion `p n`
    against the goal `p 4`, setting `n = 4` and leaving goal `Even 4`."
    apply hp
    Hint "The goal is `Even 4`, meaning `∃ r, 4 = r + r`. Provide
    the witness: `use 2`."
    use 2
  -- Part 2: 3 ∉ {n | p n}, which reduces to ¬ p 3 = (p 3 → False)
  · Hint "The goal asks that 3 is not in the p-set, which means
    `p 3 → False`. Use `intro h` to assume `p 3`."
    intro h
    Branch
      obtain ⟨r, hr⟩ := hq 3 h
      Hint "You derived and destructured in one step. The equation
      `hr : 3 = r + r` has no natural number solution. Use `omega`."
      omega
    Hint "You have `h : p 3` and `hq : ∀ n, p n → Even n`. Apply `hq`
    to `3` and `h` to derive that 3 must be even:
    `have h3 := hq 3 h`."
    Hint (hidden := true) "`have h3 := hq 3 h` gives
    `h3 : Even 3` (meaning `∃ r, 3 = r + r`)."
    have h3 := hq 3 h
    Hint "`h3 : Even 3` means there exists `r` with `3 = r + r`.
    Destructure it: `obtain ⟨r, hr⟩ := h3`."
    obtain ⟨r, hr⟩ := h3
    Hint "The equation `hr : 3 = r + r` has no solution — 3 is odd.
    `omega` derives the contradiction."
    omega

Conclusion "
Congratulations — you have completed **SetWorld**!

Here is what you now know:

| Concept | Lean definition | Proof move |
|---|---|---|
| Set | `α → Prop` | — |
| Membership `x ∈ s` | `s x` (predicate evaluation) | unfolds automatically |
| Set builder `{x \\| P x}` | `setOf (fun x => P x) = fun x => P x` | unfolds to `P x` |
| `Set.univ` | `fun _ => True` | `constructor` |
| `∅` | `fun _ => False` | impossible (`intro h; exact h`) |
| `Even n` | `∃ r, n = r + r` | `use` with witness |
| Non-membership `x ∉ s` | `¬ (s x) = s x → False` | `intro h` then contradiction |
| Compound predicate | `P x ∧ Q x` | `constructor` then prove each part |

The central insight: **sets in Lean are predicates, and set operations
reduce to logical operations.** This principle extends throughout the
course: union will correspond to `∨`, intersection to `∧`, complement
to `¬`, subset to `∀ x, ... →  ...`.

In the next world, you will learn about **subsets** and **set equality**.
The key idea will be *extensionality*: two sets are equal when they have
the same elements, which means proving `∀ x, x ∈ s ↔ x ∈ t`. The
membership skills you just mastered are exactly what those proofs require.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf
