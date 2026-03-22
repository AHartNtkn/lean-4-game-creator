import Game.Metadata

World "Cardinality"
Level 8

Title "Computing a Concrete Cardinality"

Introduction "
# Chaining the Card Lemmas

You have three tools:
- `card_empty`: $|\\emptyset| = 0$
- `card_singleton a`: $|\\{a\\}| = 1$
- `card_insert_of_notMem h`: $|\\text{insert}(a, s)| = |s| + 1$ when $a \\notin s$

To compute $|\\{1, 2, 3\\}|$, peel the finset layer by layer:

$$\\{1, 2, 3\\} = \\text{insert}\\;1\\;\\{2, 3\\}$$

So $|\\{1, 2, 3\\}| = |\\{2, 3\\}| + 1$ (since $1 \\notin \\{2, 3\\}$).

Then $\\{2, 3\\} = \\text{insert}\\;2\\;\\{3\\}$, so $|\\{2, 3\\}| = |\\{3\\}| + 1$.

Finally $|\\{3\\}| = 1$ by `card_singleton`.

Each `card_insert_of_notMem` step requires a non-membership proof.
You'll prove these yourself using the membership pattern from
FinsetBasics: assume membership, rewrite with `mem_insert`/`mem_singleton`,
and derive a contradiction.

**Your task**: Prove $|\\{1, 2, 3\\}| = 3$ from scratch.
"

/-- {1, 2, 3} has exactly 3 elements. -/
Statement : ({1, 2, 3} : Finset ℕ).card = 3 := by
  Hint "First prove that 1 is not in the finset containing 2 and 3.
  Use `have` to state it:
  `have h1 : (1 : ℕ) ∉ (insert 2 (singleton 3) : Finset ℕ) := by ...`
  (Recall that the finset notation for two elements is `insert` + `singleton`.)"
  Hint (hidden := true) "Inside the `have`, use `intro h` to assume
  membership, then `rw [Finset.mem_insert] at h` to get a disjunction.
  Case-split with `cases h with | inl h | inr h`.
  In the left branch: `omega`. In the right: `rw [Finset.mem_singleton] at h; omega`."
  have h1 : (1 : ℕ) ∉ ({2, 3} : Finset ℕ) := by
    Hint "You need to show `1 ∉ insert 2 (singleton 3)`.
    Assume membership with `intro h`."
    intro h
    Hint "Now `h : 1 ∈ insert 2 (singleton 3)`.
    Rewrite with `rw [Finset.mem_insert] at h` to get a disjunction."
    rw [Finset.mem_insert] at h
    Hint "Case-split on `h` with
    `cases h with | inl h | inr h`"
    cases h with
    | inl h => omega
    | inr h => rw [Finset.mem_singleton] at h; omega
  Hint "Now prove that 2 is not in the singleton containing 3, the same way."
  Hint (hidden := true) "`have h2 : (2 : ℕ) ∉ (singleton 3 : Finset ℕ) := by`
  then `intro h; rw [Finset.mem_singleton] at h; omega`"
  have h2 : (2 : ℕ) ∉ ({3} : Finset ℕ) := by
    Hint "Assume membership with `intro h`, then rewrite and derive
    a contradiction."
    Hint (hidden := true) "`intro h; rw [Finset.mem_singleton] at h; omega`"
    intro h
    rw [Finset.mem_singleton] at h; omega
  Hint "Now peel the insert layers using the non-membership proofs.
  `rw [Finset.card_insert_of_notMem h1]`."
  rw [Finset.card_insert_of_notMem h1]
  Hint "Peel the next layer: `rw [Finset.card_insert_of_notMem h2]`."
  rw [Finset.card_insert_of_notMem h2]
  Hint "The innermost set is a singleton: `rw [Finset.card_singleton]`."
  Hint (hidden := true) "Try `rw [Finset.card_singleton]`."
  rw [Finset.card_singleton]

Conclusion "
You computed a concrete cardinality from scratch:

1. Prove non-membership for each insert layer (retrieval from FinsetBasics)
2. `rw [card_insert_of_notMem h]` — peel each insert
3. `rw [card_singleton]` — resolve the innermost singleton

This is the full recipe for computing $|\\{a_1, \\ldots, a_n\\}|$:
prove $n - 1$ non-membership facts, apply `card_insert` that many
times, then `card_singleton` once. The arithmetic resolves automatically.

The non-membership proofs followed the FinsetBasics pattern:
assume membership, rewrite with `mem_insert`/`mem_singleton`,
and derive a contradiction with `omega`.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
