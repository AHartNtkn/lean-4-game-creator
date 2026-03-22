import Game.Metadata

World "Cardinality"
Level 16

Title "Complement Counting"

Introduction "
# Counting by Splitting

Again, the 'collect card facts, then omega' strategy applies.

Every finset `s` splits into two disjoint pieces relative to any
other finset `t`:
- The elements in both: $s \\cap t$
- The elements in `s` but not `t`: $s \\setminus t$

Since these two pieces are disjoint and their union is `s`, their
cardinalities add up to $|s|$:

$$|s \\setminus t| + |s \\cap t| = |s|$$

In Lean:
```
Finset.card_sdiff_add_card_inter s t :
    (s \\ t).card + (s ∩ t).card = s.card
```

This is **complement counting**: if you know two of the three
quantities ($|s|$, $|s \\setminus t|$, $|s \\cap t|$), you can compute
the third.

**Your task**: Given $|s| = 8$ and $|s \\cap t| = 3$, compute
$|s \\setminus t|$.
"

/-- Compute the set difference cardinality by complement counting. -/
Statement (s t : Finset ℕ) (hs : s.card = 8)
    (hi : (s ∩ t).card = 3) : (s \ t).card = 5 := by
  Hint "Apply `Finset.card_sdiff_add_card_inter s t` to get the
  splitting identity. Then use `omega` with the given sizes."
  Hint (hidden := true) "Try
  `have h := Finset.card_sdiff_add_card_inter s t` and then `omega`."
  have h := Finset.card_sdiff_add_card_inter s t
  omega

Conclusion "
Complement counting is the 'sibling' of inclusion-exclusion:
- **Inclusion-exclusion**: $|s \\cup t| + |s \\cap t| = |s| + |t|$
  — relates the union to the sum of sizes
- **Complement counting**: $|s \\setminus t| + |s \\cap t| = |s|$
  — relates the difference to the whole

Both express the idea that counting should be additive on disjoint
pieces. In fact, complement counting IS a special case of disjoint
union: $s = (s \\setminus t) \\cup (s \\cap t)$ is a disjoint
decomposition.

In plain math, this is the strategy 'count the complement':
if you want $|s \\setminus t|$, compute $|s| - |s \\cap t|$.
"

/-- `Finset.card_sdiff_add_card_inter s t` states that
`(s \\ t).card + (s ∩ t).card = s.card`.

## Syntax
```
have h := Finset.card_sdiff_add_card_inter s t
```

## When to use it
When you need to relate `(s \\ t).card` to `s.card` and
`(s ∩ t).card`. This is complement counting: the set difference
and the intersection partition `s`.

## Related
- `Finset.card_sdiff_of_subset h` — when `s ⊆ t`:
  `(t \\ s).card = t.card - s.card`
-/
TheoremDoc Finset.card_sdiff_add_card_inter as "Finset.card_sdiff_add_card_inter" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_sdiff_add_card_inter

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
