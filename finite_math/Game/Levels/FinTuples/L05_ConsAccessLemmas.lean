import Game.Metadata

World "FinTuples"
Level 5

Title "Cons Access Lemmas"

Introduction "
# Rewriting with Access Lemmas

You know that `Fin.cons a f 0 = a` and `Fin.cons a f i.succ = f i`
hold by definition. These facts have official names:

- **`Fin.cons_val_zero`**: `Fin.cons a f 0 = a`
  — the head of a cons'd tuple is the prepended element

- **`Fin.cons_val_succ`**: `Fin.cons a f i.succ = f i`
  — the tail elements are the original tuple

Why name definitional equalities? Because you'll need them for
**rewriting**. When a cons expression appears inside a hypothesis
or a larger goal, `rw [Fin.cons_val_zero]` simplifies it — even
when `rfl` alone can't close the goal.

Here, you're given a tuple `g` that equals `Fin.cons a f` via a
hypothesis. Since `g` isn't literally `Fin.cons a f`, you need to
rewrite using both `hg` and the access lemmas.

**Your task**: Use `rw [hg, Fin.cons_val_zero]` for the head,
and `rw [hg, Fin.cons_val_succ]` for the tail.
"

/-- Access a cons'd tuple through a hypothesis. -/
Statement (a : ℕ) (f : Fin 2 → ℕ) (g : Fin 3 → ℕ) (hg : g = Fin.cons a f) :
    g 0 = a ∧ ∀ i : Fin 2, g i.succ = f i := by
  Hint "Use `constructor` to split the conjunction into two goals."
  constructor
  · Hint "The goal is `g 0 = a`. Rewrite `g` using `hg`, then
    simplify with the access lemma: `rw [hg, Fin.cons_val_zero]`."
    rw [hg, Fin.cons_val_zero]
  · Hint "Start with `intro i` to introduce the index."
    intro i
    Hint "Now rewrite using `hg` and the tail access lemma:
    `rw [hg, Fin.cons_val_succ]`."
    rw [hg, Fin.cons_val_succ]

Conclusion "
You now have two named access lemmas in your inventory:

| Lemma | Statement |
|---|---|
| `Fin.cons_val_zero` | `Fin.cons a f 0 = a` |
| `Fin.cons_val_succ` | `Fin.cons a f i.succ = f i` |

The key skill: when you have a hypothesis like `hg : g = Fin.cons a f`,
chain it with an access lemma to simplify:
- `rw [hg, Fin.cons_val_zero]` turns `g 0` into `a`
- `rw [hg, Fin.cons_val_succ]` turns `g i.succ` into `f i`

This **rewrite-then-simplify** pattern will be essential in later
levels when you prove injectivity and reconstruction properties
of cons'd tuples.
"

/-- `Fin.cons_val_zero a f` states that `Fin.cons a f 0 = a`.

The head of a cons'd tuple is the prepended element.

## When to use it
When you need to simplify `Fin.cons a f 0` to `a` using `rw`.
-/
TheoremDoc Fin.cons_val_zero as "Fin.cons_val_zero" in "Fin"

/-- `Fin.cons_val_succ a f i` states that `Fin.cons a f i.succ = f i`.

The later elements of a cons'd tuple come from the original tuple.

## When to use it
When you need to simplify `Fin.cons a f i.succ` to `f i` using `rw`.
-/
TheoremDoc Fin.cons_val_succ as "Fin.cons_val_succ" in "Fin"

NewTheorem Fin.cons_val_zero Fin.cons_val_succ

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
