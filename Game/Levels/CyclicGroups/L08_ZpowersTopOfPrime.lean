import Game.Metadata

World "CyclicGroups"
Level 8

Title "zpowers in Prime-Order Groups"

Introduction
"
Time to put the pieces together. In a prime-order group, if `g ≠ 1`,
then `zpowers g` must be the whole group.

The argument:
- `zpowers g` is a subgroup, so by the prime-order dichotomy it's
  either `⊥` or `⊤`.
- If `zpowers g = ⊥`, then `g = 1` (by `zpowers_eq_bot`). But
  `g ≠ 1` — contradiction.
- So `zpowers g = ⊤`.

This is exactly the dichotomy-plus-contradiction pattern from the
last level, but now the contradiction comes from converting
`zpowers g = ⊥` to `g = 1` using `Subgroup.zpowers_eq_bot`.

Use `rw [Subgroup.zpowers_eq_bot] at hbot` to convert a hypothesis
`hbot : zpowers g = ⊥` into `hbot : g = 1`.
"

TheoremTab "Cyclic"

/-- Disabled — prove it yourself. -/
TheoremDoc zpowers_eq_top_of_prime_card as "zpowers_eq_top_of_prime_card" in "Cyclic"

DisabledTactic group
DisabledTheorem zpowers_eq_top_of_prime_card

Statement (G : Type*) [Group G] [Fact (Nat.card G).Prime]
    (g : G) (hg : g ≠ 1) : Subgroup.zpowers g = ⊤ := by
  Hint "Apply the prime-order dichotomy to `zpowers {g}`:

  `obtain hbot | htop := (Subgroup.zpowers {g}).eq_bot_or_eq_top_of_prime_card`"
  obtain hbot | htop := (Subgroup.zpowers g).eq_bot_or_eq_top_of_prime_card
  · Hint "**Case** `hbot : zpowers {g} = ⊥`: convert this to `{g} = 1`
    using `rw [Subgroup.zpowers_eq_bot] at hbot`."
    rw [Subgroup.zpowers_eq_bot] at hbot
    Hint "Now `hbot : {g} = 1` contradicts `hg : {g} ≠ 1`.

    Use `exfalso` then `exact hg hbot`."
    exfalso
    exact hg hbot
  · Hint "**Case** `htop : zpowers {g} = ⊤`: this is exactly the goal."
    Hint (hidden := true) "`exact htop`"
    exact htop

Conclusion
"
You proved that in a prime-order group, any non-identity element
generates the whole group: `zpowers g = ⊤`.

This is the **core argument** of the boss level. The only remaining
step will be wrapping it in the `IsCyclic` characterization.

Compare this proof with the last level:

| Step | L7 (abstract `H`) | L8 (`zpowers g`) |
|------|-------------------|------------------|
| Dichotomy | `H.eq_bot_or_eq_top_of_prime_card` | `(zpowers g).eq_bot_or_eq_top_of_prime_card` |
| Rule out `⊥` | `exact hne hbot` | `rw [zpowers_eq_bot] at hbot; exfalso; exact hg hbot` |
| Conclude `⊤` | `exact htop` | `exact htop` |

The extra step in the `⊥` case — converting `zpowers g = ⊥` to
`g = 1` via `zpowers_eq_bot` — is the key technique. You can't
directly apply `hg : g ≠ 1` to `hbot : zpowers g = ⊥` without
first translating between the subgroup-level and element-level
statements.
"
