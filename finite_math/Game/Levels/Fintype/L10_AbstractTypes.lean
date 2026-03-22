import Game.Metadata

World "Fintype"
Level 10

Title "Abstract Types"

Introduction "
# Working with Abstract Finite Types

So far, every type in our `card_*` exercises has been concrete: `Fin n`,
`Bool`, or a composite built from them. But the composition rules work
for ANY finite types — including abstract types whose cardinality you
know only from a hypothesis.

When you see a statement like:
```
(α : Type*) [Fintype α] (hα : Fintype.card α = 5)
```
the `[Fintype α]` tells Lean that `α` is finite (not every type is —
`ℕ` has no `Fintype` instance!), and `hα` gives you its cardinality.
You can `rw [hα]` to substitute the value, just as you'd use
`rw [Fintype.card_fin]` for `Fin n`.

**Your task**: Given a finite type `α` with `Fintype.card α = 5`,
compute the cardinality of `α ⊕ Fin 3`. You'll need `card_sum` to
decompose, the hypothesis `hα` for the left summand, and `card_fin`
for the right.
"

/-- If α has 5 elements, then α ⊕ Fin 3 has 8 elements. -/
Statement (α : Type*) [Fintype α] (hα : Fintype.card α = 5) :
    Fintype.card (α ⊕ Fin 3) = 8 := by
  Hint "Use `rw [Fintype.card_sum]` to split into
  `Fintype.card α + Fintype.card (Fin 3)`.
  Then use `rw [hα]` to replace `Fintype.card α` with `5`,
  and `rw [Fintype.card_fin]` to evaluate `Fintype.card (Fin 3)`."
  Hint (hidden := true) "Try `rw [Fintype.card_sum, hα, Fintype.card_fin]`."
  rw [Fintype.card_sum, hα, Fintype.card_fin]

Conclusion "
You combined a cardinality hypothesis (`hα`) with the composition
rules to count elements of a type built from an abstract component.

The workflow: decompose with `card_*` lemmas, then substitute known
values — whether from hypotheses (`hα`) or base-type lemmas
(`card_fin`, `card_bool`) — to reach a number.

Next: what if two types have the *same* cardinality? Bijections let us
transfer cardinality between equivalent types.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
