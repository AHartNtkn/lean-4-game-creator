import Game.Metadata

World "AbstractionLadder"
Level 13

Title "Nodup: Two Distinct Elements"

Introduction "
# Nodup for Longer Lists

You proved `[b].Nodup` using `nodup_cons`, `not_mem_nil`, and
`nodup_nil`. Now try a two-element list.

**Your task**: Prove that `[a, b]` has no duplicates, given `a ≠ b`.

The same recursive strategy applies:
1. `rw [List.nodup_cons]` to split into `a ∉ [b] ∧ [b].Nodup`
2. `constructor` to handle each part
3. For `a ∉ [b]`: assume membership, peel with `List.mem_cons`,
   case-split, and derive contradictions
4. For `[b].Nodup`: use the same pattern from the previous level

The new ingredient: deriving a contradiction from `a ≠ b` when a case
gives you `a = b`.
"

/-- A two-element list with distinct elements has no duplicates. -/
Statement (a b : ℕ) (hab : a ≠ b) : List.Nodup [a, b] := by
  Hint "Start with `rw [List.nodup_cons]` to split the nodup condition."
  rw [List.nodup_cons]
  Hint "The goal is `a ∉ [b] ∧ [b].Nodup`. Use `constructor` to split."
  constructor
  Hint "First goal: `a ∉ [b]`. This means you must show membership leads
  to a contradiction. Use `intro hmem` to assume `a ∈ [b]`."
  · Hint (hidden := true) "Try:
    `intro hmem`
    `rw [List.mem_cons] at hmem`
    Then case-split on `hmem`."
    intro hmem
    rw [List.mem_cons] at hmem
    Hint "Now `hmem : a = b ∨ a ∈ []`. Case-split with `cases hmem`."
    cases hmem with
    | inl h =>
      Hint "`h : a = b` contradicts `hab : a ≠ b`.
      Since `hab` is a function `a = b → False`, applying it to `h`
      gives a proof of `False`."
      Hint (hidden := true) "Try `exact hab h`."
      exact hab h
    | inr h =>
      Hint "`h : a ∈ []` contradicts `List.not_mem_nil`."
      Hint (hidden := true) "Try `exact List.not_mem_nil h`."
      exact List.not_mem_nil h
  Hint "Second goal: `[b].Nodup`. You proved this in the previous level.
  The same pattern works: `rw [List.nodup_cons]`, then close."
  · rw [List.nodup_cons]
    Hint "The goal is `b ∉ [] ∧ [].Nodup`. Use `constructor` to split
    the conjunction, then close each part:
    - `List.not_mem_nil` for `b ∉ []`
    - `List.nodup_nil` for `[].Nodup`"
    Hint (hidden := true) "Try:
    `constructor`
    `· exact List.not_mem_nil`
    `· exact List.nodup_nil`

    Or as a one-liner: `exact ⟨List.not_mem_nil, List.nodup_nil⟩`"
    exact ⟨List.not_mem_nil, List.nodup_nil⟩

Conclusion "
You proved a two-element list has no duplicates. The proof has two
layers of recursion:

| Step | What you proved |
|---|---|
| Outer `nodup_cons` | `[a, b].Nodup ↔ a ∉ [b] ∧ [b].Nodup` |
| `a ∉ [b]` branch | Membership leads to `a = b` (contradicts `hab`) or `a ∈ []` (impossible) |
| Inner `nodup_cons` | `[b].Nodup ↔ b ∉ [] ∧ [].Nodup` — same as previous level |

The **contradiction-from-≠** pattern is new: when you have `hab : a ≠ b`
and a case gives `h : a = b`, the term `hab h` is a proof of `False`.
This works because `a ≠ b` is definitionally `a = b → False`.

**The general pattern**: For any concrete list, you can prove `Nodup` by
recursively applying `nodup_cons`, handling the `∉` part by contradiction
(using known inequalities or `not_mem_nil`), and closing with `nodup_nil`
at the base.
"

TheoremTab "List"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith contradiction
DisabledTheorem List.perm_cons_erase List.Perm.decidable List.nodup_singleton
