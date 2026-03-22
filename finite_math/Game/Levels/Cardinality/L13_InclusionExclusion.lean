import Game.Metadata

World "Cardinality"
Level 13

Title "Inclusion-Exclusion"

Introduction "
# The Fundamental Counting Identity

When you take the union of two sets, elements in the overlap get
counted twice. The **inclusion-exclusion** principle corrects for
this double-counting:

$$|s \\cup t| + |s \\cap t| = |s| + |t|$$

In Lean:
```
Finset.card_union_add_card_inter s t :
    (s ∪ t).card + (s ∩ t).card = s.card + t.card
```

Read it as: the size of the union plus the size of the overlap equals
the sum of the individual sizes. Equivalently:

$$|s \\cup t| = |s| + |t| - |s \\cap t|$$

(but the additive form avoids natural number subtraction issues).

**Your task**: Given the sizes of `s`, `t`, and their intersection,
compute the size of their union.
"

/-- Compute the union cardinality from the individual sizes and their overlap. -/
Statement (s t : Finset ℕ) (hs : s.card = 7) (ht : t.card = 5)
    (hi : (s ∩ t).card = 3) : (s ∪ t).card = 9 := by
  Hint "Apply `Finset.card_union_add_card_inter` to get the identity
  relating the four cardinalities. Then use `omega` for the arithmetic."
  Hint (hidden := true) "Try
  `have h := Finset.card_union_add_card_inter s t` and then `omega`."
  have h := Finset.card_union_add_card_inter s t
  Hint "You have `h : (s ∪ t).card + (s ∩ t).card = s.card + t.card`.
  Combined with `hs`, `ht`, and `hi`, `omega` can solve for
  `(s ∪ t).card`."
  omega

Conclusion "
The inclusion-exclusion formula is the most important counting identity
in combinatorics. In this two-set case:

$$|A \\cup B| = |A| + |B| - |A \\cap B|$$

Why does it work? When you add $|A| + |B|$, elements in $A \\cap B$
are counted twice — once in $|A|$ and once in $|B|$. Subtracting
$|A \\cap B|$ corrects the double count.

The Lean statement uses the additive form $|A \\cup B| + |A \\cap B| = |A| + |B|$
because natural number subtraction can lose information (it floors at 0).
The additive form is unconditionally true.

**Name this proof strategy**: **collect-and-close**. You brought a
cardinality lemma into context with `have`, then let a decision
procedure (`omega`) handle the arithmetic. The mathematical thinking
goes into choosing which lemma to apply; the arithmetic is mechanical.

This pattern is not specific to cardinality — it appears throughout
the course: `have` + `omega` for linear arithmetic, `have` + `ring`
for polynomial algebra, and `have` + `ring` + `omega` for mixed cases
(you'll meet this variant in SummationFormulas). Wherever you see it,
the strategy is the same: **collect** the relevant facts into the
context, then **close** with a decision procedure.

This identity generalizes. For three sets:

$$|A \\cup B \\cup C| = |A| + |B| + |C| - |A \\cap B| - |A \\cap C| - |B \\cap C| + |A \\cap B \\cap C|$$

The alternating-sign pattern continues: for $n$ sets, there are
$2^n - 1$ correction terms.

**Connection to the partition identity**: In FinsetOperations you proved
$s = (s \\setminus t) \\cup (s \\cap t)$. Since $s \\setminus t$ and
$s \\cap t$ are disjoint, $|s| = |s \\setminus t| + |s \\cap t|$ — this is
complement counting (Level 16). Inclusion-exclusion follows: since
$s \\cup t = (s \\setminus t) \\cup t$ and this is also disjoint,
$|s \\cup t| = |s \\setminus t| + |t| = |s| - |s \\cap t| + |t|$.
The partition identity is the deeper fact; inclusion-exclusion is its
numerical consequence.
"

/-- `Finset.card_union_add_card_inter s t` states that
`(s ∪ t).card + (s ∩ t).card = s.card + t.card`.

This is the **inclusion-exclusion** formula for two sets.

## Syntax
```
have h := Finset.card_union_add_card_inter s t
```

## When to use it
When you need to relate `(s ∪ t).card` to the individual cardinalities
and their overlap. After bringing it into context, use `omega` to
derive the specific equality or inequality you need.

## Equivalent form
`(s ∪ t).card = s.card + t.card - (s ∩ t).card`
(but the additive form avoids subtraction issues on `ℕ`).
-/
TheoremDoc Finset.card_union_add_card_inter as "Finset.card_union_add_card_inter" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_union_add_card_inter

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
