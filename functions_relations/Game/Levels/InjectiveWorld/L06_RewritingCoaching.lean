import Game.Metadata

World "InjectiveWorld"
Level 6

Title "Rewriting at Hypotheses"

TheoremTab "Function"

Introduction "
# Two New Proof Moves

The next level introduces **left inverses** — functions that undo another
function. Its proof requires two rewriting techniques you have not used yet.
This level teaches them on a simple statement first.

**Move 1 — Rewriting at a hypothesis**: `rw [h] at hyp`

You already know `rw [h]`, which rewrites the **goal**. Adding `at hyp`
rewrites a **hypothesis** instead. If `h : a = b` and `hyp : P a`, then
`rw [h] at hyp` changes `hyp` to `P b`.

**Move 2 — Backward rewriting**: `rw [← h]`

Normally `rw [h]` replaces the left side with the right side.
The arrow `←` reverses direction: `rw [← h]` replaces the **right** side
with the **left** side. If `h : a = b`, then `rw [← h]` replaces `b`
with `a` in the goal.

**Your task**: Given that `g` fixes both `a` and `b` (meaning `g a = a`
and `g b = b`), and that `g a = g b`, prove `a = b`.

**Strategy**:
1. Use `rw [hab] at h₁` to update `h₁` from `g a = a` to `g b = a`
2. Use `rw [← h₁, h₂]` to transform the goal `a = b` into `b = b`
"

/-- If g fixes a and b, and g a = g b, then a = b. -/
Statement {α : Type} {g : α → α} {a b : α}
    (h₁ : g a = a) (h₂ : g b = b) (hab : g a = g b) : a = b := by
  Hint "Use `rw [hab] at h₁` to replace `g a` with `g b` in hypothesis
  `h₁`. This changes `h₁` from `g a = a` to `g b = a`."
  rw [hab] at h₁
  Hint "Now `h₁ : g b = a` and `h₂ : g b = b`. Both express `g b` as
  something, so `a` and `b` are both equal to `g b`.

  Use `rw [← h₁, h₂]`:
  - `← h₁` replaces `a` with `g b` (backward: right-to-left)
  - `h₂` replaces `g b` with `b` (forward: left-to-right)"
  Hint (hidden := true) "`rw [← h₁, h₂]`"
  Branch
    rw [← h₁]
    exact h₂
  rw [← h₁, h₂]

Conclusion "
You learned two new rewriting moves:

| Move | Effect |
|---|---|
| `rw [h] at hyp` | Rewrites hypothesis `hyp` using equation `h` |
| `rw [← h]` | Rewrites the goal using `h` right-to-left |

**The pattern you just used**: When two hypotheses share a common
expression (`g b` appears in both `h₁` and `h₂`), you can chain
`← h₁` and `h₂` to connect the other sides: `a = g b = b`.

This rewriting pattern — update a hypothesis with `rw at`, then
chain backward and forward rewrites — is the key technique for the
next level, where you will prove that left inverses imply injectivity.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Iff.rfl
