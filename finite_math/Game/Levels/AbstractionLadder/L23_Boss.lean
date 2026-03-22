import Game.Metadata

World "AbstractionLadder"
Level 23

Title "Boss: Across the Ladder"

Introduction "
# Boss: Connecting All Three Layers

This boss tests your ability to move across the abstraction ladder
in a single proof.

**The setup**: You have two lists `l₁` and `l₂` that are permutations
of each other. You know `l₁` has no duplicates.

**Your task**: Prove that `l₂.toFinset.card = l₁.length`.

This requires four facts working together:

1. **Permutations preserve nodup** (`List.Perm.nodup_iff`):
   Since `l₁` has no duplicates and `l₁ ~ l₂`, then `l₂` has no
   duplicates either.

2. **Nodup card = length** (`List.toFinset_card_of_nodup`):
   Since `l₂` has no duplicates, `l₂.toFinset.card = l₂.length`.

3. **Permutations preserve length** (`List.Perm.length_eq`):
   Since `l₁ ~ l₂`, they have the same length.

4. **Chain the equalities**: Combine steps 2 and 3.

Use `have` statements to build up intermediate facts.
"

/-- Permuted nodup lists give finsets with card equal to the original length. -/
Statement (l₁ l₂ : List ℕ) (hp : l₁.Perm l₂) (hnd : l₁.Nodup) :
    l₂.toFinset.card = l₁.length := by
  Hint "Start by showing `l₂` also has no duplicates.
  `List.Perm.nodup_iff` gives `l₁.Perm l₂ → (l₁.Nodup ↔ l₂.Nodup)`.
  Use it with `hp` and `hnd`."
  Hint (hidden := true) "Try:
  `have hnd2 : l₂.Nodup := hp.nodup_iff.mp hnd`"
  have hnd2 : l₂.Nodup := hp.nodup_iff.mp hnd
  Hint "Good. Now use `toFinset_card_of_nodup` to convert the finset
  card to a list length."
  Hint (hidden := true) "Try:
  `rw [List.toFinset_card_of_nodup hnd2]`"
  rw [List.toFinset_card_of_nodup hnd2]
  Hint "The goal is now `l₂.length = l₁.length`. The equation is
  backwards: `hp.length_eq` gives `l₁.length = l₂.length`. Two options:
  - Use `rw [← hp.length_eq]` to rewrite right-to-left (as in L08)
  - Use `exact hp.length_eq.symm` to flip the equation directly"
  Hint (hidden := true) "Try `rw [← hp.length_eq]` to rewrite the goal,
  or `exact hp.length_eq.symm` to close it directly."
  Branch
    rw [← hp.length_eq]
  exact hp.length_eq.symm

Conclusion "
You traversed the full abstraction ladder in one proof:

| Step | Tool | What it did |
|---|---|---|
| 1 | `Perm.nodup_iff` | Transferred nodup across the permutation |
| 2 | `toFinset_card_of_nodup` | Converted finset card to list length |
| 3 | `Perm.length_eq` | Equated the two list lengths |

This proof touched all three layers:
- **List layer**: `Nodup`, `length`, `Perm`
- **Multiset layer**: The permutation quotient (implicit in `toFinset`)
- **Finset layer**: `.card` of the resulting finset

The abstraction ladder is not just a theoretical construction — it's
a practical proof tool. When you need to reason about finset
cardinality, you can descend to the list level, use list-level tools
(permutations, nodup, length), and bring the results back up.

**Your toolkit from this world**:

| Concept | Key lemma |
|---|---|
| List length | `length_cons`, `length_append` |
| List membership | `mem_cons` |
| Permutation | `Perm.swap`, `Perm.cons`, `Perm.trans` |
| Perm → equal length | `Perm.length_eq` |
| Perm → equal finsets | `toFinset_eq_of_perm` |
| Nodup (no duplicates) | `nodup_cons`, `nodup_nil` |
| Perm preserves nodup | `Perm.nodup_iff` |
| List → Multiset | `Multiset.coe_eq_coe` |
| Multiset card | `Multiset.card_cons`, `coe_card` |
| List → Finset | `List.toFinset`, `mem_toFinset` |
| Nodup card = length | `toFinset_card_of_nodup` |

**A note on `Finset.map`**: You may encounter `Finset.map` in Mathlib.
It works like `Finset.image` but bundles an injectivity proof with the
function (using `Function.Embedding`). Since `map` knows the function
is injective, it can skip deduplication — making it more efficient
internally. The relationship is `Finset.map_eq_image`: for injective
functions, `map` and `image` give the same result.

**What's next**: The `Fintype` world uses this abstraction ladder to
count elements of composite types like products and function spaces.
"

TheoremTab "List"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
