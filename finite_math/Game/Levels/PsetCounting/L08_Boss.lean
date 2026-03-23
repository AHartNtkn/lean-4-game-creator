import Game.Metadata

World "PsetCounting"
Level 8

Title "Boss: The Full Argument"

Introduction "
You have a function `f : α → β` that is injective, and a
classification function `g : β → Fin 3` that sorts elements
of `β` into three categories.

You know `Fintype.card α = 10`. Prove that some category must
contain more than 3 elements of `β`.

No shortcuts -- you must build the full argument.
"

/-- Injecting 10 elements into β, then classifying β into
3 categories, forces some category to have more than 3 elements. -/
Statement {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (g : β → Fin 3)
    (hinj : Function.Injective f)
    (hα : Fintype.card α = 10) :
    ∃ c : Fin 3,
      3 < (Finset.univ.filter (fun b : β => g b = c)).card := by
  -- Step 1: Contradiction setup
  Hint "What happens if no category has more than 3 elements?"
  Hint (hidden := true) "Try `by_contra hall`."
  by_contra hall
  Hint (hidden := true) "Try `push_neg at hall`."
  push_neg at hall
  -- hall : ∀ c, (univ.filter ...).card ≤ 3
  -- Step 2: Injection bound
  Hint (hidden := true) "What does the injection `f` tell you
  about the size of `β`? Try
  `have hle := Fintype.card_le_of_injective f hinj`."
  have hle := Fintype.card_le_of_injective f hinj
  -- Step 3: Fiber decomposition
  Hint (hidden := true) "Express `Fintype.card β` as a sum of
  category sizes. Start with:
  `have hmem : ∀ b ∈ (Finset.univ : Finset β), g b ∈ (Finset.univ : Finset (Fin 3)) := fun _ _ => Finset.mem_univ _`"
  have hmem : ∀ b ∈ (Finset.univ : Finset β),
    g b ∈ (Finset.univ : Finset (Fin 3)) := fun _ _ => Finset.mem_univ _
  Hint (hidden := true) "Try
  `have hfib := Finset.card_eq_sum_card_fiberwise hmem`."
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  Hint (hidden := true) "Try `rw [Finset.card_univ] at hfib`."
  rw [Finset.card_univ] at hfib
  -- Step 4: Bound the sum
  Hint (hidden := true) "Bound the sum using your assumption:
  `have hbound := Finset.sum_le_sum (fun (c : Fin 3) (_ : c ∈ Finset.univ) => hall c)`"
  have hbound := Finset.sum_le_sum
    (fun (c : Fin 3) (_ : c ∈ Finset.univ) => hall c)
  Hint (hidden := true) "Try:
  `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound`"
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hbound
  -- Step 5: Contradiction
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
Congratulations! You completed the **Counting Techniques
Problem Set**.

**The proof chain**:

| Step | Result |
|------|--------|
| `by_contra` + `push_neg` | Assume all categories have at most 3 |
| Injection bound | `card α ≤ card β`, so `card β ≥ 10` |
| Fiber decomposition | `card β = sum of category sizes` |
| Sum bound | `sum ≤ 3 * 3 = 9` |
| Arithmetic | `10 ≤ card β = sum ≤ 9` -- contradiction |

The injection bound (recall L03's duality table) converts
the injectivity hypothesis into a numerical lower bound on
`card β`. This is the information chaining pattern from L07:
one function's property constrains a type's size, then that
constraint feeds into the counting argument.

**Three strategies for negative goals**: This world used
three different approaches to prove negation:
- **Direct witness** (L02): extract colliding elements,
  then show injectivity fails via `hne (hinj heq)`
- **Assume and derive absurdity** (L03): use the positive
  assumption (surjectivity/injectivity) to derive an
  impossible inequality
- **`by_contra` + `push_neg`** (L05, this level): negate
  the existential to get a universal bound, then contradict
  it with a counting argument

Each strategy suits its context: direct witnesses when the
collision is extractable, assume-and-contradict when one
bound suffices, and `by_contra` + `push_neg` when you need
to transform a negated existential into a usable universal.

**Looking ahead**: These Fintype-level counting theorems
(`card_le_of_injective`, `card_eq_sum_card_fiberwise`) have
Finset-level counterparts. In the **Finale**, you'll combine
both levels of abstraction with big-operator algebra and
finset operations from earlier in the course.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Fintype.card_of_bijective Fintype.card_congr Fintype.exists_ne_map_eq_of_card_lt Fintype.not_injective_of_card_lt Equiv.ofBijective
