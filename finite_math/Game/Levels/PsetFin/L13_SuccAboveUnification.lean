import Game.Metadata

World "PsetFin"
Level 13

Title "The succAbove Unification"

Introduction "
# Two Decompositions, One Operation

In Levels 11-12, you proved two decompositions of `Fin (n + 1)`:
- **castSucc/last**: every element is either `Fin.last n` or `j.castSucc` for some `j`
- **0/succ**: every element is either `0` or `j.succ` for some `j`

Level 12's conclusion mentioned `Fin.succAbove p` — an embedding
`Fin n -> Fin (n+1)` that 'skips' position `p`. Now you'll prove
the two key facts that unify the decompositions:

1. `Fin.succAbove (Fin.last n) = Fin.castSucc` — skipping the last position IS castSucc
2. `Fin.succAbove 0 = Fin.succ` — skipping position 0 IS succ

This turns a pattern observation into a theorem: both `castSucc`
and `succ` are special cases of the single 'skip one position'
operation `succAbove`.

**Your task**: Prove both equalities.
"

/-- succAbove at last is castSucc, and succAbove at 0 is succ. -/
Statement (n : ℕ) :
    Fin.succAbove (Fin.last n) = Fin.castSucc ∧
    Fin.succAbove (0 : Fin (n + 1)) = Fin.succ := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "The first part is `Fin.succAbove_last` — skipping the last
    position gives `castSucc`.
    Use `exact Fin.succAbove_last`."
    exact Fin.succAbove_last
  · Hint "The second part is `Fin.succAbove_zero` — skipping position 0
    gives `succ`.
    Use `exact Fin.succAbove_zero`."
    exact Fin.succAbove_zero

Conclusion "
You've proved the **succAbove unification**: both `castSucc` and `succ`
are special cases of `Fin.succAbove p`.

| Boundary | `p` | `succAbove p` | Decomposition |
|---|---|---|---|
| Top | `Fin.last n` | `Fin.castSucc` | castSucc/last |
| Bottom | `0` | `Fin.succ` | 0/succ |

This is the mathematical punchline of Phase 1's embedding story.
The two decompositions you proved in L11-L12 aren't just 'dual' — they're
instances of a single pattern: decompose `Fin (n+1)` into the
image of `succAbove p` plus the singleton `{p}`.

The general decomposition `Fin (n+1) = succAbove p '' Fin n ∪ {p}`
holds for ANY `p : Fin (n+1)`, not just the endpoints. This means
you can decompose `Fin (n+1)` by skipping any position, not just
the first or last. The endpoint cases are the ones with the cleanest
names (`castSucc`, `succ`), which is why the course started there.
"

/-- `Fin.succAbove_last` states that
`Fin.succAbove (Fin.last n) = Fin.castSucc`.

Skipping the last position is the same as `castSucc` — the embedding
that includes `Fin n` into `Fin (n+1)` by leaving the value unchanged.
-/
TheoremDoc Fin.succAbove_last as "Fin.succAbove_last" in "Fin"

/-- `Fin.succAbove_zero` states that
`Fin.succAbove (0 : Fin (n+1)) = Fin.succ`.

Skipping position 0 is the same as `succ` — the embedding that shifts
every value up by 1.
-/
TheoremDoc Fin.succAbove_zero as "Fin.succAbove_zero" in "Fin"

/-- `Fin.succAbove p` is the order-preserving embedding
`Fin n -> Fin (n+1)` that skips position `p`.

It unifies `castSucc` and `succ`:
- `succAbove (last n) = castSucc`
- `succAbove 0 = succ`
-/
DefinitionDoc Fin.succAbove as "Fin.succAbove"

NewTheorem Fin.succAbove_last Fin.succAbove_zero
NewDefinition Fin.succAbove

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases
DisabledTheorem funext
