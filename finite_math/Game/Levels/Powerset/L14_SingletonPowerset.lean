import Game.Metadata

World "Powerset"
Level 14

Title "Powerset of a Singleton"

Introduction "
# Base Case: 1 Element, 2 Subsets

Level 3 showed that `{1, 2}` has 4 subsets ($2^2 = 4$).
Level 13 showed that `∅` has 1 subset ($2^0 = 1$).

Now fill in the gap: a singleton set `{1}` has exactly 2 subsets
($2^1 = 2$) — the empty set and the set itself.

This completes the base-case picture:
| Elements | Subsets |
|:-:|:-:|
| 0 | 1 |
| 1 | 2 |
| 2 | 4 |

Each time you add an element, the subset count doubles — every
existing subset either includes or excludes the new element.

**Your task**: Prove `(({1} : Finset ℕ).powerset).card = 2`.
Lean can compute this directly.
"

/-- A singleton finset has exactly 2 subsets. -/
Statement : (({1} : Finset ℕ).powerset).card = 2 := by
  Hint "Lean can compute the cardinality of a concrete finset's powerset
  directly. Use `decide` to let Lean verify this by computation."
  Hint (hidden := true) "Try `decide`."
  decide

Conclusion "
One step: `decide`.

Lean computed: `({1} : Finset ℕ).powerset = {∅, {1}}` and `2 = 2`. ✓

**The doubling pattern**: Every time you add one element to a set,
each existing subset splits into two versions — one with the new
element and one without. So the number of subsets doubles:

| Set | Subsets | Count |
|:-:|:--|:-:|
| `∅` | `∅` | 1 |
| `{1}` | `∅, {1}` | 2 |
| `{1,2}` | `∅, {1}, {2}, {1,2}` | 4 |

This doubling is why the total is $2^n$ — you make $n$ independent
binary choices.
"

TheoremTab "Finset"

-- Enable decide for this concretization level only
DisabledTactic trivial native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
