import Game.Metadata

World "CyclicGroups"
Level 7

Title "Subgroups of Prime-Order Groups"

Introduction
"
Here is a remarkable fact: in a group of prime order, every subgroup
is either trivial (`⊥`) or the whole group (`⊤`). There is no
room for anything in between.

`Subgroup.eq_bot_or_eq_top_of_prime_card :
  [Fact (Nat.card G).Prime] → (H : Subgroup G) → H = ⊥ ∨ H = ⊤`

Why? By Lagrange's theorem (which you'll prove later), the size of
any subgroup divides the size of the group. If the group has prime
order `p`, the only divisors of `p` are `1` and `p` — so the
subgroup has size `1` (it's `⊥`) or size `p` (it's `⊤`).

The hypothesis `[Fact (Nat.card G).Prime]` is a **typeclass**
saying \"it is a fact that `Nat.card G` is prime.\" Lean synthesizes
it automatically when it's in scope.

This level also introduces the `exfalso` tactic. When the current
hypotheses are contradictory, `exfalso` changes any goal to `False`.
You then prove `False` by combining the contradictory hypotheses.

Given a non-trivial subgroup in a prime-order group, show it must
be the whole group.
"

/-- The `exfalso` tactic changes any goal to `False`.

Use this when the current hypotheses are contradictory. After
`exfalso`, prove `False` by combining contradictory hypotheses.

Example: if `h₁ : g = 1` and `h₂ : g ≠ 1`, then after `exfalso`,
use `exact h₂ h₁` (since `h₂ : g = 1 → False` applied to `h₁`
gives `False`). -/
TacticDoc exfalso

NewTactic exfalso

/-- `Subgroup.eq_bot_or_eq_top_of_prime_card` says that in a
group of prime order, every subgroup is either `⊥` or `⊤`:

`(H : Subgroup G) → H = ⊥ ∨ H = ⊤`

This requires `[Fact (Nat.card G).Prime]` — Lean must know the
group's cardinality is prime.

Apply it to a specific subgroup to get the disjunction, then
case-split with `obtain`. -/
TheoremDoc Subgroup.eq_bot_or_eq_top_of_prime_card as "Subgroup.eq_bot_or_eq_top_of_prime_card" in "Cyclic"

NewTheorem Subgroup.eq_bot_or_eq_top_of_prime_card

TheoremTab "Cyclic"

DisabledTactic group

Statement (G : Type*) [Group G] [Fact (Nat.card G).Prime]
    (H : Subgroup G) (hne : H ≠ ⊥) : H = ⊤ := by
  Hint "Apply the prime-order dichotomy to `H`:

  `obtain hbot | htop := H.eq_bot_or_eq_top_of_prime_card`

  This gives you `H = ⊥ ∨ H = ⊤`, and `obtain` with `|` splits
  a disjunction into two goals — one for each case."
  obtain hbot | htop := H.eq_bot_or_eq_top_of_prime_card
  · Hint "**Case** `hbot : H = ⊥`: but `hne : H ≠ ⊥` — contradiction.

    Use `exfalso` to change the goal to `False`."
    exfalso
    Hint "Now prove `False`. You have `hne : H ≠ ⊥` (which means
    `H = ⊥ → False`) and `hbot : H = ⊥`. Apply `hne` to `hbot`:
    `exact hne hbot`."
    exact hne hbot
  · Hint "**Case** `htop : H = ⊤`: this is exactly the goal."
    Hint (hidden := true) "`exact htop`"
    exact htop

Conclusion
"
In a prime-order group, every subgroup has order dividing `p`, and
the only divisors of a prime are `1` and `p`. So every subgroup is
either trivial or the whole group.

The proof used three moves:
1. **Dichotomy** — `H.eq_bot_or_eq_top_of_prime_card` gives `H = ⊥ ∨ H = ⊤`
2. **Case split** — `obtain hbot | htop` creates two goals
3. **Contradiction** — `exfalso` + `exact hne hbot` rules out the impossible case

This **dichotomy-plus-contradiction** pattern is one of the most
common proof shapes in finite group theory: get a disjunction from
a structural theorem, then rule out one case using extra information.

For `∨` case splitting, `obtain` uses `|` instead of `⟨_, _⟩`:

| Hypothesis type | Syntax | Effect |
|-----------------|--------|--------|
| `h : A ∧ B` | `obtain ⟨hA, hB⟩ := h` | Get both components |
| `h : ∃ x, P x` | `obtain ⟨x, hx⟩ := h` | Get witness + proof |
| `h : A ∨ B` | `obtain hA \\| hB := h` | Split into two goals |

Next: you'll apply this pattern specifically to `zpowers g`.
"
