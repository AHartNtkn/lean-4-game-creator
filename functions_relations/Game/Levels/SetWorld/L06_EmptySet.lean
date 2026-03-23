import Game.Metadata

World "SetWorld"
Level 6

Title "The Empty Set"

Introduction "
# The Empty Set

The **empty set** `∅ : Set α` is the set with no elements.
Its predicate is `fun _ => False` — it returns `False` for every input.

So `n ∈ (∅ : Set ℕ)` reduces to `False`. Since `False` has no proof,
nothing can ever be a member of `∅`.

Your task is to prove that NO natural number belongs to `∅`. The
statement is `∀ n : ℕ, n ∉ ∅`.

The proof has two layers:
1. `intro n` — introduce the universally quantified `n`
2. `intro h` — since `n ∉ ∅` is `¬ (n ∈ ∅)` which is `n ∈ ∅ → False`,
   introduce the hypothesis `h : n ∈ ∅`
3. Now `h` has type `False` (since `n ∈ ∅` reduces to `False`),
   and the goal is `False`, so `exact h` finishes.

**Your task**: Prove the statement step by step.
"

/-- No natural number belongs to the empty set. -/
Statement : ∀ n : ℕ, n ∉ (∅ : Set ℕ) := by
  Hint "Start with `intro n` to introduce the universally quantified
  variable."
  intro n
  Hint "The goal is `n ∉ ∅`, which means `n ∈ ∅ → False`. Use
  `intro h` to assume `n ∈ ∅`."
  intro h
  Hint "Now `h` has type `False` (because `n ∈ ∅` reduces to `False`).
  The goal is also `False`. Use `exact h`."
  Hint (hidden := true) "`exact h` closes the goal since `h` has
  exactly the type `False`."
  exact h

Conclusion "
The empty set `∅` is defined by the predicate `fun _ => False`, so
membership always reduces to `False`.

The proof pattern:
- `∀ n, n ∉ ∅` means `∀ n, n ∈ ∅ → False`
- After `intro n` and `intro h`, the hypothesis `h` has type `False`
  (because `n ∈ ∅` IS `False`)
- `exact h` closes the goal

Notice that `intro` handled TWO different things here: first a universal
quantifier (`∀ n`), then an implication (`→ False`). Both work because
under the Curry-Howard correspondence, `∀ x, P x` and `P → Q` are
both function types — `intro` is the same operation in both cases.

Also note the *ex falso* principle at work: if you have `h : False`,
then `exact h` closes ANY goal, not just `False`. Here the goal
happened to be `False`, but if it were `0 = 1` or anything else,
`exact h` would still work. `False` implies everything — this is
*ex falso quodlibet* (from falsehood, anything follows).

Compare with Level 1: there, `Set.univ` had predicate `fun _ => True`,
so membership was trivially provable. Here, `∅` has predicate
`fun _ => False`, so membership is impossible. The two sets are
mirror images.
"

/-- `∅ : Set α` is the empty set — the set containing no elements.

It is defined as `fun _ => False`, so `x ∈ (∅ : Set α)` reduces to
`False`.

## Syntax
```
(∅ : Set α)     -- empty set (typed \\emptyset)
```

## Example
`n ∈ (∅ : Set ℕ)` reduces to `False`.
`n ∉ (∅ : Set ℕ)` reduces to `¬ False`, which is `False → False`.

## Related
- `Set.notMem_empty x` is the proof that `x ∉ (∅ : Set α)`
- `Set.univ` is the opposite extreme: everything is a member
-/
DefinitionDoc EmptyCollection.emptyCollection as "∅"

NewDefinition EmptyCollection.emptyCollection

/-- `Set.notMem_empty x` proves `x ∉ ∅` for any `x`. -/
TheoremDoc Set.notMem_empty as "Set.notMem_empty" in "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.notMem_empty Set.mem_setOf_eq Set.mem_setOf
