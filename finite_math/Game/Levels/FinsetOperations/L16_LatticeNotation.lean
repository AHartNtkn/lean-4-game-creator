import Game.Metadata

World "FinsetOperations"
Level 16

Title "Lattice Notation"

Introduction "
# New Tactics: `show` and `change`

Before tackling the main topic, you need two new tactics:

**`show`** replaces the current goal with a definitionally equal
statement. If the goal displays as `x ∈ s ⊔ t`, you can write
`show x ∈ s ∪ t` and Lean accepts it because `⊔` and `∪` are
the same operation. The goal's *meaning* is unchanged; only the
*notation* changes.

**`change ... at h`** does the same for a hypothesis. If
`h : x ∈ s ⊓ t`, then `change x ∈ s ∩ t at h` rewrites the
hypothesis to use `∩` notation instead.

Both tactics work whenever the old and new expressions are
*definitionally equal* — the same value, just written differently.

# Lattice Notation: ⊔ and ⊓

In Lean, finset union and intersection are implemented through the
**lattice** structure. This means you'll sometimes see alternative
notation in the infoview:

- `s ⊔ t` is the same as `s ∪ t` (lattice 'supremum' = union)
- `s ⊓ t` is the same as `s ∩ t` (lattice 'infimum' = intersection)

These are **exactly the same operations** — just different notation.

**The problem**: `rw [Finset.mem_union]` matches `∪` but not `⊔`.
When lattice notation appears, you need to convert it first using
`show` (for the goal) or `change` (for hypotheses). After
converting, all the familiar membership lemmas work normally.

You may also encounter `≤` in place of `⊆` (lattice order = subset).
The same `show`/`change` technique handles it.

**Your task**: Given `x ∈ s ⊓ t` (intersection via lattice notation),
prove `x ∈ s ⊔ t` (union via lattice notation).
"

/-- From intersection to union via lattice notation. -/
Statement (s t : Finset ℕ) (x : ℕ) (h : x ∈ s ⊓ t) : x ∈ s ⊔ t := by
  Hint "The goal uses `⊔` (lattice supremum = union). Convert it
  to familiar notation with `show x ∈ s ∪ t`."
  show x ∈ s ∪ t
  Hint "The hypothesis uses `⊓` (lattice infimum = intersection).
  Convert it with `change x ∈ s ∩ t at h`."
  change x ∈ s ∩ t at h
  Hint "Now both goal and hypothesis use familiar notation.
  Use `rw [Finset.mem_inter] at h` and `rw [Finset.mem_union]`."
  rw [Finset.mem_inter] at h
  rw [Finset.mem_union]
  Hint (hidden := true) "Choose `left` and use `exact h.1`."
  left
  exact h.1

Conclusion "
The key insight: `⊔` = `∪` and `⊓` = `∩` for finsets, but `rw`
can't see through the notation difference. Use `show` (goal) or
`change` (hypothesis) to convert lattice notation to finset notation
before rewriting.

The workflow when you encounter lattice notation:
1. **Recognize** `⊔` as union and `⊓` as intersection
2. **Convert** with `show`/`change` to familiar notation
3. **Proceed** with `rw [Finset.mem_union]` etc. as usual

In the next level, you'll learn `simp only` — a tool for unfolding
multiple membership layers at once.
"

NewTactic «show» «change»

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self and_comm or_comm inf_le_left inf_le_right le_sup_left le_sup_right
