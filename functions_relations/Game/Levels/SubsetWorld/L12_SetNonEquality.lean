import Game.Metadata

World "SubsetWorld"
Level 12

Title "Disproving Set Equality"

Introduction "
# When Two Sets Are Not Equal

In Levels 10–11, you proved set equalities using `ext`. But what if
two sets are NOT equal? How do you prove `s ≠ t`?

In Lean, `s ≠ t` is defined as `(s = t) → False`. So to prove
`s ≠ t`, you use `intro h` to **assume** the sets are equal, getting
`h : s = t`, and then derive a contradiction (`False`).

The strategy mirrors Level 7 (disproving `⊆`): **find a witness** that
leads to contradiction. If `s = t`, then every element of `s` is in `t`
and vice versa. Find an element that is in one set but not the other —
then the assumption `s = t` forces a false arithmetic conclusion.

In this level, you will prove `{n | n < 3} ≠ {n | n < 5}`. The
witness is `3`: it satisfies `3 < 5` (so `3` is in the right set) but
not `3 < 3` (so `3` is not in the left set). If the sets were equal,
`3` would have to be in both — contradiction.

**Proof plan**:
1. `intro h` — assume the sets are equal
2. Prove `3 ∈ {n | n < 5}` — show the witness is in the right set
3. Use `rw [← h]` to transport: if equal, `3 ∈ {n | n < 3}`
4. Unwrap and derive contradiction — `3 < 3` is false
"

/-- The set of numbers less than 3 is not equal to the set of
numbers less than 5. -/
Statement : {n : ℕ | n < 3} ≠ {n : ℕ | n < 5} := by
  Hint "The goal is `s ≠ t`, which means `(s = t) → False`.
  Use `intro h` to assume the sets are equal and aim for a contradiction."
  intro h
  Hint "Now `h` says the two sets are equal. Find a witness that breaks
  this — an element in one set but not the other. The number `3` works:
  `3 < 5` is true but `3 < 3` is false.

  First, establish that 3 is in the right set. Prove membership by
  showing `(3 : ℕ) < 5` using `show` and `omega`."
  Hint (hidden := true) "Step by step:
  1. `have h5 : (3 : ℕ) < 5 := by omega`
  2. `rw [← h] at h5`
  3. `change (3 : ℕ) < 3 at h5`
  4. `omega`"
  have h5 : (3 : ℕ) ∈ {n : ℕ | n < 5} := by show (3 : ℕ) < 5; omega
  Hint "Good — `h5` proves 3 is in the right set. Now use the equality
  `h` to transport this membership to the other set. Rewriting with
  `rw [← h] at h5` replaces the right set with the left set in `h5`.

  (`← h` rewrites backward: if `h : A = B`, then `← h` replaces `B`
  with `A`.)"
  rw [← h] at h5
  Hint "`h5` now says `3` is in the left set, which is definitionally
  `3 < 3`. Unwrap with `change (3 : ℕ) < 3 at h5`, then `omega`
  derives `False` from `3 < 3`."
  change (3 : ℕ) < 3 at h5
  Hint "`h5 : 3 < 3` is clearly false. `omega` can derive `False`
  from contradictory arithmetic."
  omega

Conclusion "
You proved your first set **non-equality**! The proof structure was:

1. **Assume** the sets are equal (`intro h`)
2. **Exhibit** a witness element (3)
3. **Transport** membership using the equality (`rw [← h]`)
4. **Derive contradiction** from the impossible conclusion (`3 < 3`)

Compare this with Level 7 (disproving `⊆`):

| Goal | Assume | Witness | Contradiction from |
|---|---|---|---|
| `¬ (s ⊆ t)` | `h : s ⊆ t` | element in `s` but not `t` | applying `h` to witness |
| `s ≠ t` | `h : s = t` | element in one but not other | rewriting with `h` |

Both use the same strategy — assume and contradict — but the mechanism
differs. For `⊆`, you apply the subset hypothesis as a function. For
`=`, you rewrite with the equality hypothesis to transport membership.

In ordinary math: \"Suppose `{n | n < 3} = {n | n < 5}`. Then
`3 ∈ {n | n < 3}` (since `3 ∈ {n | n < 5}` and the sets are equal).
But `3 < 3` is false. Contradiction.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.ext_iff
