import Game.Metadata

World "Powerset"
Level 9

Title "Complements Stay in the Powerset"

Introduction "
# The Complement Map

If `t` is a subset of `s`, then removing `t` from `s` gives the
**complement** `s \\ t` — the elements of `s` that are *not* in `t`.
This complement is also a subset of `s`, so it is also in the
powerset.

This means the powerset is closed under complementation:
$$t \\in \\mathcal{P}(s) \\implies s \\setminus t \\in \\mathcal{P}(s)$$

This is the structural explanation behind the symmetry
$\\binom{n}{k} = \\binom{n}{n-k}$ that you will prove in the boss:
choosing which $k$ elements to *include* is the same as choosing
which $n - k$ elements to *exclude*. The complement map is the
bijection that witnesses this symmetry.

**Your task**: Given `ht : t ∈ s.powerset`, prove `s \\ t ∈ s.powerset`.

Strategy:
1. Convert the hypothesis using `mem_powerset` (Level 5 pattern)
2. Convert the goal using `mem_powerset`
3. Close with `Finset.sdiff_subset` — the set difference is always
   a subset of the parent set

**A question to keep in mind**: Does the proof actually need the
hypothesis `ht`? Watch for whether you use it or not.
"

/-- `Finset.sdiff_subset` states that `s \\ t ⊆ s` — removing
elements from a set gives a subset.

## Syntax
```
exact Finset.sdiff_subset
```

## When to use it
When the goal is `s \\ t ⊆ s` for any finsets `s` and `t`.

## Meaning
The set difference `s \\ t` keeps only elements of `s` that
are not in `t`, so the result is always a subset of `s`.
-/
TheoremDoc Finset.sdiff_subset as "Finset.sdiff_subset" in "Finset"

/-- The complement of a powerset member is also in the powerset. -/
Statement (s t : Finset ℕ) (ht : t ∈ s.powerset) : s \ t ∈ s.powerset := by
  Hint "First, convert `ht` from powerset membership to a subset
  claim using `Finset.mem_powerset`. This is the Level 5 pattern."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at ht`."
  rw [Finset.mem_powerset] at ht
  Hint "Now `ht : t ⊆ s`. Convert the goal to a subset claim too."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset]`."
  rw [Finset.mem_powerset]
  Hint "The goal is `s \\ t ⊆ s`. The set difference removes elements
  from `s`, so the result is always a subset. Use `Finset.sdiff_subset`."
  Hint (hidden := true) "Try `exact Finset.sdiff_subset`."
  exact Finset.sdiff_subset

Conclusion "
Three steps:
1. `rw [mem_powerset] at ht` — see that `t ⊆ s`
2. `rw [mem_powerset]` — convert goal to `s \\ t ⊆ s`
3. `exact Finset.sdiff_subset` — the set difference is a subset

**Why this matters**: The powerset is closed under complementation.
For every subset `t` of `s`, the complement `s \\ t` (the elements
you *did not* choose) is also a subset of `s`. This pairs every
`k`-element subset with an `(n-k)`-element subset, which is exactly
the bijection behind the symmetry $\\binom{n}{k} = \\binom{n}{n-k}$.

**Did you notice?** The proof did not actually use `ht`. The fact
`s \\ t ⊆ s` holds for *any* `t`, not just subsets of `s`. This is
an important mathematical observation: **not every hypothesis is
necessary**. Spotting unnecessary hypotheses is a valuable skill —
it tells you the result is more general than stated.

So why did we include `ht`? Because the *mathematical story* needs
it. We care about complementation as an operation on the powerset:
given a subset `t` of `s`, produce another subset `s \\ t` of `s`.
The hypothesis `ht : t ∈ s.powerset` frames the result as a closure
property of the complement map on $\\mathcal{P}(s)$. The next two
levels will use `ht` essentially — Level 10 needs `t ⊆ s` to
compute the complement's cardinality, and Level 11 needs it to
prove the complement is an involution.
"

NewTheorem Finset.sdiff_subset

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
