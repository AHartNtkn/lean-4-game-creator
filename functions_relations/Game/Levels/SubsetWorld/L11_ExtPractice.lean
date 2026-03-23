import Game.Metadata

World "SubsetWorld"
Level 11

Title "Ext Practice"

Introduction "
# Practice: Another Set Equality

The sets `{n : ℕ | n ≤ 2}` and `{n | n < 3}` contain exactly the
same natural numbers: $\\{0, 1, 2\\}$. Prove they are equal.

Both directions require arithmetic reasoning: `n ≤ 2 ↔ n < 3` for
natural numbers. Unlike Level 10, neither direction is trivial — you
will need `change` and `omega` in both.

**Proof plan**:
1. `ext x` — reduce to membership `↔`
2. `constructor` — split into two directions
3. Each direction: `intro`, `change` to unwrap, `show` to unwrap
   the goal, `omega` to close
"

/-- The set of naturals at most 2 equals the set of naturals less than 3. -/
Statement : {n : ℕ | n ≤ 2} = {n : ℕ | n < 3} := by
  Hint "Use `ext x` to start the set equality proof."
  ext x
  Hint "Now `constructor` to split the `↔`."
  constructor
  -- Forward: x ≤ 2 → x < 3
  · Hint "Assume membership in the left set. Then unwrap both sides
    and use arithmetic."
    intro hx
    Hint "You have `hx` saying `x` is in the left set (i.e., `x ≤ 2`)
    and the goal says `x` is in the right set (i.e., `x < 3`).
    Use `change x ≤ 2 at hx` and `show x < 3` to unwrap both,
    then `omega`."
    Hint (hidden := true) "After `change x ≤ 2 at hx` and
    `show x < 3`, the goal `x < 3` follows from `x ≤ 2` by `omega`."
    change x ≤ 2 at hx
    show x < 3
    omega
  -- Backward: x < 3 → x ≤ 2
  · Hint "The backward direction is similar: unwrap and use arithmetic."
    intro hx
    Hint "Unwrap `hx` with `change x < 3 at hx` and the goal with
    `show x ≤ 2`, then close with `omega`."
    Hint (hidden := true) "`change x < 3 at hx` then `show x ≤ 2`
    then `omega`."
    change x < 3 at hx
    show x ≤ 2
    omega

Conclusion "
Both directions followed the same pattern: unwrap hypothesis, unwrap
goal, close with arithmetic. Call this the **unwrap-and-close** pattern:
`change` to reveal the arithmetic, `show` to reveal the goal, then a
closer like `omega`. This pattern will recur whenever set descriptions
involve arithmetic predicates.

Notice how symmetric the proof was — both directions used the same
three-step structure. This symmetry is typical when the set descriptions
are equivalent arithmetic conditions.

In plain math: $n \\leq 2$ if and only if $n < 3$ (for natural numbers).
This is because $\\leq$ and $<$ differ by exactly 1 on the integers,
and there are no naturals between 2 and 3.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.Subset.antisymm le_antisymm HasSubset.Subset.antisymm subset_antisymm Set.eq_of_subset_of_subset LE.le.antisymm Set.ext_iff
