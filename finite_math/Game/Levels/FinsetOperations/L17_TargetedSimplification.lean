import Game.Metadata

World "FinsetOperations"
Level 17

Title "Targeted Simplification"

Introduction "
# simp only: Targeted Rewriting

You've been unfolding membership one `rw` at a time:
```
rw [Finset.mem_union] at h
rw [Finset.mem_insert] at h
rw [Finset.mem_insert] at h
rw [Finset.mem_singleton] at h
```

This works but it's tedious. Lean has a better tool: `simp only`.

`simp only [lemma₁, lemma₂, ...]` applies the listed lemmas as rewrite
rules **repeatedly** until no more apply. Unlike bare `simp` (which uses
a large default set of lemmas and can be unpredictable), `simp only`
uses *only* the lemmas you specify. This makes it:
- **Targeted**: you control exactly which rewrites happen
- **Predictable**: no surprise simplifications
- **Efficient**: replaces multiple `rw` calls with one `simp only`

`simp only` also works on hypotheses: `simp only [...] at h` rewrites
the hypothesis `h`.

**Note**: Bare `simp` (without `only`) is now available, and it will work
on some goals. But `simp only` is the skill being taught here — it gives
you control over exactly which lemmas are applied, which makes proofs
more readable and maintainable.

**Your task**: An element `x` is in `{{1, 2, 3}} ∪ {{4, 5}}`. Prove
that `x ∈ Finset.range 6`.

Use `simp only` to unfold the union and concrete memberships in `h`
in one step, then close with `rw [Finset.mem_range]; omega`.
"

/-- If x ∈ {1, 2, 3} ∪ {4, 5}, then x ∈ range 6. -/
Statement (x : ℕ) (h : x ∈ ({1, 2, 3} : Finset ℕ) ∪ ({4, 5} : Finset ℕ)) :
    x ∈ Finset.range 6 := by
  Hint "Use `simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h`
  to unfold the union and concrete memberships in `h` all at once."
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
  Hint "Now `h` is a disjunction of equalities: `x` equals one of
  `1, 2, 3, 4, 5`. The goal is `x ∈ Finset.range 6`.
  Rewrite with `rw [Finset.mem_range]` to get `x < 6`, then `omega`
  closes it from the disjunctive hypothesis."
  rw [Finset.mem_range]
  omega

Conclusion "
`simp only` replaced four or more `rw` calls plus case splitting with
a single line. After `simp only [mem_union, mem_insert, mem_singleton] at h`,
the hypothesis `h` becomes a pure disjunction of equalities — all the
finset structure is gone.

**When to use simp only**:
- When you need to unfold multiple membership layers at once
- When the manual `rw` chain would be tedious
- When you want the result to be pure logic (∨, ∧, ¬)

**Key rule**: Always use `simp only [...]` with an explicit lemma list,
not bare `simp`. Bare `simp` uses hundreds of default lemmas and can
produce unpredictable results. `simp only` gives you control.

**Common lemma list for finset membership**:
```
simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
           Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
           Finset.mem_range]
```

You'll use `simp only` in the upcoming levels to simplify membership
rewrites before tackling the logic.
"

NewTactic simp

DisabledTactic trivial «decide» native_decide aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self inf_le_left inf_le_right le_sup_left le_sup_right
