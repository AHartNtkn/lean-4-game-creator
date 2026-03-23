import Game.Metadata

World "CountingTechniques"
Level 14

Title "Concrete Double Counting"

Introduction "
# Double Counting in Action

Levels 11-13 taught fiber decomposition on abstract types.
Now apply it to a concrete scenario with real numbers.

**Problem**: A teacher assigns 7 students to 3 study groups.
Each group can have at most 2 students. Is this possible?

No! **Double counting** reveals the contradiction:
- **Direct count**: there are 7 students
- **Fiber count**: the sum of group sizes is at most 3 * 2 = 6

The same set of students is counted two ways, but the counts
disagree: 7 vs. at most 6. So the assignment is impossible.

This is double counting at its most visceral: count the same
thing two ways, compare the results, and when they conflict,
conclude impossibility.

**Proof plan** (using the tools from Levels 11-13):
1. Membership proof: every student maps into `Finset.univ`
2. Fiber decomposition: `7 = sum of group sizes`
3. Sum bound: each group size <= 2, so `sum <= 3 * 2 = 6`
4. Contradiction: `7 <= 6` is false

**Your task**: Prove this assignment is impossible.
"

/-- Seven students can't fit into three groups of at most two. -/
Statement (assign : Fin 7 → Fin 3)
    (hgroups : ∀ g : Fin 3,
      (Finset.univ.filter (fun s : Fin 7 => assign s = g)).card ≤ 2) :
    False := by
  Hint "First, establish that every student maps into `Finset.univ`.
  This is the membership proof needed for fiber decomposition."
  Hint (hidden := true) "Try:
  `have hmem : forall x in (Finset.univ : Finset (Fin 7)), assign x in (Finset.univ : Finset (Fin 3)) := fun _ _ => Finset.mem_univ _`"
  have hmem : ∀ x ∈ (Finset.univ : Finset (Fin 7)),
    assign x ∈ (Finset.univ : Finset (Fin 3)) := fun _ _ => Finset.mem_univ _
  Hint "Apply fiber decomposition to express the total number of
  students as a sum of group sizes."
  Hint (hidden := true) "Try:
  `have hfib := Finset.card_eq_sum_card_fiberwise hmem`"
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  Hint "Simplify: `(Finset.univ).card = Fintype.card (Fin 7) = 7`."
  Hint (hidden := true) "Try:
  `rw [Finset.card_univ, Fintype.card_fin] at hfib`"
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  Hint "Now bound the sum. Since each group has at most 2 students
  (`hgroups`), use `Finset.sum_le_sum` to bound the total."
  Hint (hidden := true) "Try:
  `have hbound := Finset.sum_le_sum (fun (g : Fin 3) (_ : g in Finset.univ) => hgroups g)`"
  have hbound := Finset.sum_le_sum (fun (g : Fin 3) (_ : g ∈ Finset.univ) => hgroups g)
  Hint "Simplify the constant sum: `sum g in univ, 2 = 3 * 2 = 6`."
  Hint (hidden := true) "Try:
  `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound`"
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  Hint "Now `hfib : 7 = sum ...` and `hbound : sum ... <= 6`.
  Together: `7 <= 6`, which is absurd."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
Concrete double counting:
1. Membership proof: `fun _ _ => Finset.mem_univ _`
2. `card_eq_sum_card_fiberwise` -- 7 = sum of group sizes
3. `sum_le_sum` -- bound each group by 2
4. `sum_const` + `smul_eq_mul` -- total bound = 3 * 2 = 6
5. `omega` -- 7 <= 6 is absurd

**Why double counting works**: You counted the same set (7 students)
two ways:
- Directly: 7 students
- By groups: sum of 3 group sizes, each at most 2

The counts must agree, but they can't: 7 vs. at most 6.
This conflict proves the assignment is impossible.

**The pattern**: Double counting is most powerful when it reveals
contradictions. The abstract machinery (fiber decomposition +
sum bounds) is the engine, but the insight is always the same:
**count the same thing two ways and compare**.

**Classic examples**:
- The handshake lemma: sum of vertex degrees = 2 * number of edges
- Committee counting: count student-committee pairs by students
  vs. by committees
- Counting lattice paths: the same path count gives a binomial
  identity

Whenever you see 'how many X satisfy Y?', ask: can I count
the X-Y pairs two different ways?
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
