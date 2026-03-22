import Game.Metadata

World "AbstractionLadder"
Level 10

Title "Multiset Count"

Introduction "
# What Multisets Remember: Multiplicities

Multisets forget order but **remember duplicates**. The function
`Multiset.count a m` tells you how many times `a` appears in `m`.

Two key lemmas:
- `Multiset.count_cons_self : count a (a ::ₘ s) = count a s + 1`
  — consing the element you're counting adds 1
- `Multiset.count_cons_of_ne : a ≠ b → count a (b ::ₘ s) = count a s`
  — consing a different element doesn't change the count

**Your task**: Count how many times `a` appears in a multiset where
`a` and `b` (with `a ≠ b`) are both consed onto a multiset `s`.
You'll need both lemmas: `count_cons_of_ne` to skip past `b`, and
`count_cons_self` to count `a`.
"

/-- Counting through cons: skip different elements, count matching ones. -/
Statement (a b : ℕ) (s : Multiset ℕ) (hab : a ≠ b)
    (h : Multiset.count a s = 3) :
    Multiset.count a (b ::ₘ a ::ₘ s) = 4 := by
  Hint "The outer cons is `b`, which is different from `a`.
  Use `rw [Multiset.count_cons_of_ne hab]` to skip past it."
  rw [Multiset.count_cons_of_ne hab]
  Hint "Now the inner cons is `a`, matching what we're counting.
  Use `rw [Multiset.count_cons_self]` to peel it off and add 1."
  rw [Multiset.count_cons_self]
  Hint "The goal is `Multiset.count a s + 1 = 4`. Use the hypothesis
  `h` to substitute the count."
  Hint (hidden := true) "Try `rw [h]` or `omega`."
  rw [h]

Conclusion "
You used both count lemmas:
- `count_cons_of_ne` to skip past elements that don't match
- `count_cons_self` to count elements that do match

Together, these two lemmas let you compute `count` for any
explicit multiset by peeling off elements one at a time.

The cardinality of a multiset (`Multiset.card`) is its total number of
elements including duplicates:
- `Multiset.card_cons : (a ::ₘ m).card = m.card + 1`
- `Multiset.coe_card : (↑l).card = l.length`

**Key distinction**: `count` tells you how many times a *specific*
element appears. `card` tells you the *total* number of elements.
"

/-- `Multiset.card` returns the number of elements in a multiset,
counting duplicates.

## Key lemmas
- `Multiset.card_cons : (a ::ₘ m).card = m.card + 1`
- `Multiset.card_zero : (0 : Multiset α).card = 0`
- `Multiset.coe_card : (↑l).card = l.length`
-/
DefinitionDoc Multiset.card as "Multiset.card"

/-- `Multiset.card_cons` states that
`(a ::ₘ m).card = m.card + 1`.

## Syntax
```
rw [Multiset.card_cons]
```

## When to use it
When the goal involves the cardinality of a cons'd multiset.
-/
TheoremDoc Multiset.card_cons as "Multiset.card_cons" in "Multiset"

/-- `Multiset.count a m` returns the number of times `a` appears in `m`.

## Key lemmas
- `Multiset.count_cons_self : count a (a ::ₘ s) = count a s + 1`
- `Multiset.count_cons_of_ne : a ≠ b → count a (b ::ₘ s) = count a s`
-/
DefinitionDoc Multiset.count as "Multiset.count"

/-- `Multiset.count_cons_self` states that
`Multiset.count a (a ::ₘ s) = Multiset.count a s + 1`.

Consing the element you're counting adds 1 to the count.

## Syntax
```
rw [Multiset.count_cons_self]
```
-/
TheoremDoc Multiset.count_cons_self as "Multiset.count_cons_self" in "Multiset"

/-- `Multiset.count_cons_of_ne hab` states that
`Multiset.count a (b ::ₘ s) = Multiset.count a s`
when `hab : a ≠ b`.

Consing a different element doesn't change the count.

## Syntax
```
rw [Multiset.count_cons_of_ne hab]
```
-/
TheoremDoc Multiset.count_cons_of_ne as "Multiset.count_cons_of_ne" in "Multiset"

/-- `Multiset.coe_card l` states that `(↑l : Multiset α).card = l.length`.

Coercing a list to a multiset preserves the element count.

## Syntax
```
rw [Multiset.coe_card]
exact Multiset.coe_card l
```

## When to use it
When you need to connect multiset cardinality to list length.
-/
TheoremDoc Multiset.coe_card as "Multiset.coe_card" in "Multiset"

TheoremTab "Multiset"
NewDefinition Multiset.card Multiset.count
NewTheorem Multiset.card_cons Multiset.coe_card Multiset.count_cons_self Multiset.count_cons_of_ne

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem List.perm_cons_erase List.Perm.decidable
