import Game.Metadata

World "PsetCardinality"
Level 11

Title "Boss: Four Counting Principles"

Introduction "
# Boss: Integrating Across All Four Worlds

This boss tests whether you can identify and apply counting
techniques from all four prerequisite worlds — Cardinality,
Abstraction Ladder, Fintype, and CountingTypes — in a single proof.

**The setup**: You have finsets, a list, an abstract type, and
injections. The goal is a sum of four quantities equaling 20.

**Your task**: Figure out which technique computes each piece,
compute them, and let `omega` combine the results.

No further guidance — this is a pset boss. Plan the decomposition
yourself.
"

/-- Four counting techniques combine to prove a single equation. -/
Statement (s t : Finset ℕ) (hs : s.card = 5) (ht : t.card = 4)
    (hi : (s ∩ t).card = 2)
    (l : List ℕ) (hnd : l.Nodup) (hlen : l.length = 3)
    (α : Type*) [Fintype α] (e : α ≃ Fin 2 × Bool) :
    (s ∪ t).card + l.toFinset.card + Fintype.card α + Fintype.card (Fin 2 ↪ Fin 3) = 20 := by
  Hint "Four separate counting computations feed into one equation.
  Each term in the sum needs a different technique. Start by
  identifying which world's tools apply to each piece."
  Hint (hidden := true) "The four pieces decompose as:
  1. (s ∪ t).card — inclusion-exclusion (Cardinality): 5 + 4 - 2 = 7
  2. l.toFinset.card — nodup bridge (Abstraction Ladder): length = 3
  3. Fintype.card α — equivalence + decomposition (Fintype): 2 * 2 = 4
  4. Fintype.card (Fin 2 ↪ Fin 3) — falling factorial (CountingTypes): 3 * 2 = 6
  Compute each in a `have` block, then `omega`."
  Hint (hidden := true) "Start with inclusion-exclusion:
  `have h1 := Finset.card_union_add_card_inter s t`"
  have h1 := Finset.card_union_add_card_inter s t
  Hint (hidden := true) "Bridge the list length to finset cardinality:
  `have h2 := List.toFinset_card_of_nodup hnd`"
  have h2 := List.toFinset_card_of_nodup hnd
  Hint (hidden := true) "Compute the type cardinality via equivalence:
  `have h3 : Fintype.card α = 4 := by`
  then resolve with `rw` steps inside the sub-proof."
  have h3 : Fintype.card α = 4 := by
    Hint "Resolve α via the equivalence, then decompose."
    Hint (hidden := true) "Try `rw [Fintype.card_congr e]`."
    rw [Fintype.card_congr e]
    Hint (hidden := true) "Try `rw [Fintype.card_prod]`."
    rw [Fintype.card_prod]
    Hint (hidden := true) "Try `rw [Fintype.card_fin]`."
    rw [Fintype.card_fin]
    Hint (hidden := true) "Try `rw [Fintype.card_bool]`."
    rw [Fintype.card_bool]
  Hint (hidden := true) "Count the injections:
  `have h4 : Fintype.card (Fin 2 ↪ Fin 3) = 6 := by`
  then use `card_embedding_eq` and unfold the falling factorial."
  have h4 : Fintype.card (Fin 2 ↪ Fin 3) = 6 := by
    Hint "Convert to falling factorial, evaluate, then unfold."
    Hint (hidden := true) "Try `rw [Fintype.card_embedding_eq]`."
    rw [Fintype.card_embedding_eq]
    Hint (hidden := true) "Try `rw [Fintype.card_fin]`."
    rw [Fintype.card_fin]
    Hint (hidden := true) "Try `rw [Fintype.card_fin]`."
    rw [Fintype.card_fin]
    Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
    rw [Nat.descFactorial_succ]
    Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
    rw [Nat.descFactorial_succ]
    Hint (hidden := true) "Try `rw [Nat.descFactorial_zero]`."
    rw [Nat.descFactorial_zero]
  Hint "You have all four facts. `omega` combines them."
  omega

Conclusion "
You integrated four counting techniques — one from each prerequisite
world — in a single proof:

| Component | Technique | World | Value |
|---|---|---|---|
| $(s \\cup t).\\text{card}$ | inclusion-exclusion | Cardinality | 7 |
| $l.\\text{toFinset}.\\text{card}$ | nodup bridge | Abstraction Ladder | 3 |
| $\\text{Fintype.card}\\;\\alpha$ | equivalence + decomposition | Fintype | 4 |
| $|\\text{Fin}\\;2 \\hookrightarrow \\text{Fin}\\;3|$ | falling factorial | CountingTypes | 6 |

The proof strategy: compute each piece in a `have` block using the
appropriate technique, then let `omega` combine the arithmetic.

**Your toolkit from Phases 2-3**:

| Tool | What it does |
|---|---|
| `card_union_add_card_inter` | inclusion-exclusion for finsets |
| `card_sdiff_add_card_inter` | complement counting for finsets |
| `card_le_card` | monotonicity (subset → cardinality bound) |
| `card_erase_of_mem` | erasing subtracts 1 |
| `card_union_of_disjoint` | disjoint union cardinality |
| `toFinset_card_of_nodup` | nodup list length = finset card |
| `card_congr e` | equivalence → equal cardinality |
| `card_prod` | $|\\alpha \\times \\beta| = |\\alpha| \\cdot |\\beta|$ |
| `card_sum` | $|\\alpha \\oplus \\beta| = |\\alpha| + |\\beta|$ |
| `card_fun` | $|\\alpha \\to \\beta| = |\\beta|^{|\\alpha|}$ |
| `card_subtype_compl` | $|\\neg P| = |\\alpha| - |P|$ |
| `card_embedding_eq` | $|\\alpha \\hookrightarrow \\beta| = |\\beta|^{\\underline{|\\alpha|}}$ |
| `ext` | prove finset equality from element-wise membership |

**Looking ahead**: Every cardinality computation you've done can be
rephrased as a sum: $|s| = \\sum_{x \\in s} 1$. This identity —
trivial-looking but powerful — is the bridge between counting
(Phase 3) and summing (Phase 4). When you learn the big sum operator
$\\sum_{x \\in s} f(x)$, you'll see that `card` is just the special
case where $f(x) = 1$. The collect-and-close pattern you've mastered
here will generalize to `have + ring` for algebraic sums.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf

-- Force full recursive unfolding of descFactorial
DisabledTheorem Nat.descFactorial_one Nat.descFactorial_self sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
