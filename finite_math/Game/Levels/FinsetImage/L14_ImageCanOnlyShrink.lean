import Game.Metadata

World "FinsetImage"
Level 14

Title "Image Can Only Shrink"

Introduction "
# Cardinality of Images

The **cardinality** of a finset `s`, written `s.card`, is the number
of elements it contains. For example, `({1,2,3} : Finset ℕ).card = 3`
and `(Finset.range 5).card = 5`.

A key fact about images:

$$|f(S)| \\leq |S|$$

In Lean: `Finset.card_image_le : (s.image f).card ≤ s.card`

Why? The image can never have MORE elements than the input — at best,
each input maps to a distinct output. But if two inputs map to the
same output (i.e., $f$ is not injective), the image shrinks.

You saw this concretely:
- Levels 9-11: constant function mapped $\\{1,2,3\\}$ to $\\{0\\}$
  ($3 \\to 1$)
- Level 10: $n \\mapsto n-1$ mapped $\\{0,1,2,3\\}$ partially ($4 \\to 3$)

**Your task**: Given that `s` has at most `n` elements, prove that
the image `s.image f` also has at most `n` elements.

Strategy: use `Finset.card_image_le` to get
`(s.image f).card ≤ s.card`, then chain with the given bound using
`omega`.
"

/-- If s has at most n elements, so does its image under f. -/
Statement (f : ℕ → ℕ) (s : Finset ℕ) (n : ℕ) (h : s.card ≤ n) :
    (s.image f).card ≤ n := by
  Hint "Use `have him : (s.image f).card ≤ s.card := Finset.card_image_le`
  to get the key inequality."
  Hint (hidden := true) "Alternatively, `exact le_trans Finset.card_image_le h`
  closes the goal in one step."
  have him : (s.image f).card ≤ s.card := Finset.card_image_le
  Hint "Now you have `him : (s.image f).card ≤ s.card` and
  `h : s.card ≤ n`. Chain them with `omega`."
  omega

Conclusion "
`Finset.card_image_le` states that the image can never be larger
than the input:

$$|f(S)| \\leq |S|$$

This is a **non-strict** inequality — equality holds when $f$ is
injective (one-to-one) on $S$. The next level covers this case.

The proof pattern when chaining cardinality bounds:
1. Bring relevant inequalities into context with `have`
2. Use `omega` to combine them

In plain math: $|f(S)| \\leq |S| \\leq n$.

**The contrapositive as pigeonhole**: Read `card_image_le`
backwards. If $|f(S)| < |S|$, then $f$ is NOT injective on $S$
— meaning two elements of $S$ must collide. This is the
**pigeonhole principle** for finite sets: more inputs than
distinct outputs forces a collision.
"

/-- `s.card` is the number of elements in the finset `s`.

## Syntax
`s.card` or `Finset.card s` — returns a natural number.

## Examples
- `(Finset.range n).card = n`
- `({a} : Finset α).card = 1`
- `(∅ : Finset α).card = 0`

The full cardinality API (card_insert, card_erase, inclusion-exclusion)
is covered in a later world. For now, you need `card` only to state
and apply `card_image_le` and `card_image_of_injective`.
-/
DefinitionDoc Finset.card as "Finset.card"

/-- `Finset.card_image_le` states that `(s.image f).card ≤ s.card`.

The image of a finset under any function has at most as many
elements as the original finset.

## Syntax
```
have h := Finset.card_image_le  -- implicit s and f
have h : (s.image f).card ≤ s.card := Finset.card_image_le  -- explicit
```

## When to use it
When you need an upper bound on the size of an image.
Equality holds when `f` is injective (see `card_image_of_injective`).
-/
TheoremDoc Finset.card_image_le as "Finset.card_image_le" in "Finset"

NewDefinition Finset.card
NewTheorem Finset.card_image_le

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
