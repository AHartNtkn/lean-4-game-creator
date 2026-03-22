import Game.Metadata

World "FinsetBasics"
Level 8

Title "Range: The Reverse Direction"

Introduction "
# From Membership to Inequality

In Level 7, you proved the forward direction: `i < n` implies
`i ∈ Finset.range n`. Now prove the **reverse**: if
`i ∈ Finset.range n`, then `i < n`.

This completes the characterization:
$$i \\in \\texttt{Finset.range } n \\;\\Longleftrightarrow\\; i < n$$

The forward direction (Level 7) says the bound is *sufficient* for
membership. The reverse says membership *implies* the bound. Together
they say: membership in `Finset.range n` is exactly the same predicate
as being less than `n` — the same predicate that defines `Fin n`.

**Strategy**: Rewrite the hypothesis `h` using `Finset.mem_range`
to extract the inequality.
"

/-- Membership in Finset.range n implies the element is less than n. -/
Statement (n i : ℕ) (h : i ∈ Finset.range n) : i < n := by
  Hint "Rewrite `{h}` to extract the inequality:
  `rw [Finset.mem_range] at h`."
  rw [Finset.mem_range] at h
  Hint "Now `{h}` says `i < n`, which is exactly the goal."
  exact h

Conclusion "
Both directions of `Finset.mem_range` are now concrete:

| Direction | Statement | Proof |
|---|---|---|
| Forward (Level 7) | `i < n → i ∈ range n` | `rw [mem_range]; exact h` |
| Reverse (this level) | `i ∈ range n → i < n` | `rw [mem_range] at h; exact h` |

Together: **`i ∈ Finset.range n` if and only if `i < n`**.

This is the bridge between `Fin n` and `Finset.range n` made fully
explicit. An element of `Fin n` carries a proof `val < n`; membership
in `Finset.range n` is equivalent to `< n`. The two interfaces — typed
indices and set membership — encode the same information.

In later worlds, you'll use this reverse direction when given a
membership hypothesis `h : i ∈ Finset.range n` and needing to
extract the arithmetic bound for use with `omega` or other lemmas.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
