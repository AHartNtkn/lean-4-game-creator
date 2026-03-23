import Game.Metadata

World "CountingTechniques"
Level 17

Title "Generalized Pigeonhole"

Introduction "
# The Generalized Pigeonhole Principle

Level 8 proved the basic pigeonhole principle: if `n > m`, then
no function `Fin n -> Fin m` is injective (some two inputs collide).

Level 16 proved a special case of the generalized version: if
`n + 1` items go into `n` bins, some bin has at least 2 items.

Now we prove the **full generalized pigeonhole principle**: if
`m * k < n` items are distributed among `m` bins, then some bin
contains more than `k` items.

**Example**: Among 100 people, some birth month has at least
`ceiling(100 / 12) = 9` people. Here `m = 12` (months),
`n = 100` (people), `k = 8`, and `12 * 8 = 96 < 100`.

**Proof strategy** (same as Level 16's averaging argument):
1. `by_contra` + `push_neg` -- assume every bin has at most `k` items
2. Fiber decomposition -- `n = sum of bin sizes`
3. `sum_le_sum` -- sum of bin sizes <= m * k
4. But `m * k < n`, contradiction

**Your task**: Prove the generalized pigeonhole principle.
"

/-- If m * k < n items go into m bins, some bin has more than k items. -/
Statement (m k n : ℕ) (hlt : m * k < n) (f : Fin n → Fin m) :
    ∃ b : Fin m, k < (Finset.univ.filter (fun a : Fin n => f a = b)).card := by
  Hint "Start with proof by contradiction: assume no bin has more
  than `k` items."
  Hint (hidden := true) "Try `by_contra hall`."
  by_contra hall
  Hint "Use `push_neg` to transform `hall` from
  `not (exists b, k < ...)` into `forall b, ... <= k`."
  Hint (hidden := true) "Try `push_neg at hall`."
  push_neg at hall
  Hint "Establish the membership proof for fiber decomposition."
  Hint (hidden := true) "Try:
  `have hmem : forall x in (Finset.univ : Finset (Fin n)), f x in (Finset.univ : Finset (Fin m)) := fun _ _ => Finset.mem_univ _`"
  have hmem : ∀ x ∈ (Finset.univ : Finset (Fin n)),
    f x ∈ (Finset.univ : Finset (Fin m)) := fun _ _ => Finset.mem_univ _
  Hint "Apply fiber decomposition."
  Hint (hidden := true) "Try:
  `have hfib := Finset.card_eq_sum_card_fiberwise hmem`"
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  Hint "Simplify: the left side is `Fintype.card (Fin n) = n`."
  Hint (hidden := true) "Try:
  `rw [Finset.card_univ, Fintype.card_fin] at hfib`"
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  Hint "Bound the sum using `hall`: each bin has at most `k` items."
  Hint (hidden := true) "Try:
  `have hbound := Finset.sum_le_sum (fun (b : Fin m) (_ : b in Finset.univ) => hall b)`"
  have hbound := Finset.sum_le_sum (fun (b : Fin m) (_ : b ∈ Finset.univ) => hall b)
  Hint "Simplify the constant sum: `sum b in univ, k = m * k`."
  Hint (hidden := true) "Try:
  `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound`"
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  Hint "Now `hfib : n = sum ...` and `hbound : sum ... <= m * k` and
  `hlt : m * k < n`. Together: `n <= m * k < n`, contradiction."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
The generalized pigeonhole principle:
1. `by_contra` + `push_neg` -- assume all bins have at most `k` items
2. Membership proof: `fun _ _ => Finset.mem_univ _`
3. `card_eq_sum_card_fiberwise` -- `n = sum of bin sizes`
4. `sum_le_sum` -- bound sum by constant `k` per bin
5. `sum_const` + `smul_eq_mul` -- total bound = `m * k`
6. `omega` -- `n <= m * k < n` is absurd

**Compare with Level 16**: Level 16 proved the special case
`k = 1` (with `n + 1` items in `n` bins, some bin has >= 2).
This level generalizes: with `n > m * k` items in `m` bins,
some bin has more than `k`.

**In plain mathematics**: The Generalized Pigeonhole Principle
states:

> If $n$ items are placed into $m$ containers and $n > mk$,
> then some container holds more than $k$ items.

Equivalently, some container holds at least $\\lceil n/m \\rceil$
items. The proof is the averaging argument: if every container
held at most $k$ items, the total would be at most $mk < n$,
contradicting the known total.

**Applications**:
- Among 100 people, at least 9 share a birth month
  ($12 \\times 8 = 96 < 100$)
- In a deck of 52 cards, any hand of 5 has at least 2 of the
  same suit ($4 \\times 1 = 4 < 5$)
- Among any 27 English words, at least 2 start with the same
  letter ($26 \\times 1 = 26 < 27$)
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
-- Force the fiber approach — disable direct pigeonhole
DisabledTheorem Fintype.not_injective_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
