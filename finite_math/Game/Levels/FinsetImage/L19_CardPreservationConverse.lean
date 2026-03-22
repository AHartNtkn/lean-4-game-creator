import Game.Metadata

World "FinsetImage"
Level 19

Title "Size Preservation Implies Injectivity"

Introduction "
# The Converse: A Finite-Math Equivalence

Level 13 proved that injective functions preserve cardinality:

$$f \\text{ injective} \\implies |f(S)| = |S|$$

This level addresses the **converse**: if $|f(S)| = |S|$, must $f$
be injective on $S$?

For finite sets, the answer is **yes**. This is a deep fact about
finiteness: if a function doesn't lose any elements (same cardinality),
it can't have any collisions (must be injective). In Mathlib:

```
Finset.card_image_iff : (s.image f).card = s.card ↔ Set.InjOn f ↑s
```

`Set.InjOn f ↑s` means `f` is injective when restricted to `s`:
for all `a ∈ s` and `b ∈ s`, if `f a = f b` then `a = b`.

**Your task**: Given that the image preserves cardinality (`hcard`),
and two elements `a, b ∈ s` with `f a = f b`, prove `a = b`.

Strategy: convert `hcard` from a cardinality equation to an
injectivity statement using `Finset.card_image_iff`, then apply it.
"

/-- If card is preserved, equal outputs imply equal inputs. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ)
    (hcard : (s.image f).card = s.card)
    (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (heq : f a = f b) :
    a = b := by
  Hint "The key step: convert `hcard` from a cardinality equation
  to an injectivity statement.

  Use `rw [Finset.card_image_iff] at hcard` to transform
  `hcard : (s.image f).card = s.card`
  into
  `hcard : Set.InjOn f ↑s`."
  rw [Finset.card_image_iff] at hcard
  Hint "Now `hcard : Set.InjOn f ↑s`, which means
  `∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b`.

  You have `ha : a ∈ s`, `hb : b ∈ s`, and `heq : f a = f b`.
  Apply `hcard` to these: `exact hcard ha hb heq`."
  exact hcard ha hb heq

Conclusion "
This is the **fundamental equivalence** of finite-set images:

$$|f(S)| = |S| \\iff f \\text{ is injective on } S$$

The forward direction ($\\Leftarrow$) is Level 13's
`card_image_of_injective`. The backward direction ($\\Rightarrow$)
is the converse you just used.

This equivalence is **unique to finite sets** — for infinite sets,
a function can preserve 'size' (cardinality) while not being
injective (e.g., $n \\mapsto \\lfloor n/2 \\rfloor$ maps $\\mathbb{N}$
onto $\\mathbb{N}$ but is not injective).

The equivalence connects several themes:
- **Pigeonhole principle** (PsetFin): if you map $n+1$ pigeons
  into $n$ holes, two must collide — contrapositive of the
  converse direction
- **Counting arguments**: size preservation is a test for
  injectivity without checking every pair
- **Finite type theory**: `Fintype.card_congr` will generalize
  this from `Finset` to `Fintype`

**Transferable strategy — counting proves injectivity**: When you
need to show a function is injective on a finite set, you have
two approaches: (1) check every pair of inputs (often tedious),
or (2) count the image and show $|f(S)| = |S|$. Approach (2)
is often dramatically easier — you'll see it in action next level.

In the next level, you'll see this equivalence in action: using
cardinality to prove injectivity for a function where checking
every pair directly would be tedious. The backward direction
($\\Rightarrow$) is especially powerful: it lets you prove
injectivity by counting, avoiding the need to check every pair
of inputs.

You'll use `card_image_iff` again in the Cardinality world,
where counting arguments routinely convert between cardinality
equations and injectivity statements.
"

/-- `Finset.card_image_iff` states that
`(s.image f).card = s.card ↔ Set.InjOn f ↑s`.

The image of a finset preserves cardinality if and only if the
function is injective on the set.

## Syntax
```
rw [Finset.card_image_iff] at hcard  -- convert card eq to injectivity
```

## When to use it
When you need to convert between a cardinality equation and an
injectivity statement on a finset.
-/
TheoremDoc Finset.card_image_iff as "Finset.card_image_iff" in "Finset"

/-- `Set.InjOn f s` means `f` is injective when restricted to `s`:
for all `a ∈ s` and `b ∈ s`, `f a = f b → a = b`.

## Definition
```
Set.InjOn f s := ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b
```

## Relationship to `Function.Injective`
- `Function.Injective f` is global: for ALL `a b`.
- `Set.InjOn f s` is local: only for `a b ∈ s`.
- Every injective function is injective on any set.
-/
DefinitionDoc Set.InjOn as "Set.InjOn"

NewDefinition Set.InjOn
NewTheorem Finset.card_image_iff

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
