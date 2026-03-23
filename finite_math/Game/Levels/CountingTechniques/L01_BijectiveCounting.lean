import Game.Metadata

World "CountingTechniques"
Level 1

Title "Bijective Counting as a Technique"

Introduction "
# Counting Techniques: The Big Four

Welcome to the final lecture world. You've already learned the
*tools* of finite mathematics — `Fin`, `Finset`, `Fintype`,
big operators, binomial coefficients, induction. Now we learn
the four major *techniques* for combinatorial proofs:

1. **Bijective counting**: prove two sets have equal cardinality
   by constructing a bijection
2. **Injection/surjection bounds**: prove cardinality inequalities
   via injections or surjections
3. **The pigeonhole principle**: if more items than containers,
   some container holds two items
4. **Double counting** (fiber decomposition): compute the same
   quantity two different ways

You already have `Fintype.card_congr` in your inventory from the
Fintype world. This level revisits it as a *technique* — a tool
you reach for when you need to prove two types have the same size.

**The bijective proof pattern**:
1. Construct an `Equiv` (bijection) between the two types
2. Apply `Fintype.card_congr` to conclude equal cardinality
3. Evaluate the known side

**Your task**: Given an equivalence `e : α ≃ β` and the
cardinality of `β`, determine the cardinality of `α`.
"

/-- If α ≃ β and β has 10 elements, then α has 10 elements. -/
Statement (α β : Type*) [Fintype α] [Fintype β] (e : α ≃ β)
    (hβ : Fintype.card β = 10) :
    Fintype.card α = 10 := by
  Hint "Use the equivalence to transfer the cardinality.
  `rw [Fintype.card_congr e]` replaces `Fintype.card α` with
  `Fintype.card β`."
  Hint (hidden := true) "Try `rw [Fintype.card_congr e]`."
  rw [Fintype.card_congr e]
  Hint "Now the goal is `Fintype.card β = 10`. You have this
  as hypothesis `hβ`."
  Hint (hidden := true) "Try `exact hβ`."
  exact hβ

Conclusion "
Bijective counting in two steps:
1. `rw [Fintype.card_congr e]` — transfer via the equivalence
2. `exact hβ` — use the known cardinality

**When to reach for this technique**: Whenever you need to prove
`|A| = |B|` and the two types look structurally different but
have a natural correspondence. The hard part is constructing the
`Equiv` — the cardinality conclusion is mechanical.

**In plain mathematics**: The Bijection Principle says that if
there exists a one-to-one correspondence between sets $A$ and $B$,
then $|A| = |B|$. This is the most fundamental counting technique:
instead of counting directly, find a bijection to something you
already know how to count.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
