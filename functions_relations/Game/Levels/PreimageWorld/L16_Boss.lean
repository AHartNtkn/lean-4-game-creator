import Game.Metadata

World "PreimageWorld"
Level 16

Title "Boss: Composing Library Results"

TheoremTab "Set"

Introduction "
# Boss: Preimage Preserves Difference — By Composition

You have built a library of preimage identities. Now USE them.

$$f^{-1}(s \\setminus t) = f^{-1}(s) \\setminus f^{-1}(t)$$

The key insight: set difference IS intersection with complement.
The theorem `Set.diff_eq` states `s \\ t = s ∩ tᶜ`.

So the proof strategy is pure rewriting — no `ext`, no `constructor`,
no case analysis. Just compose the results you already proved:

1. `rw [Set.diff_eq]` — rewrite `s \\ t` as `s ∩ tᶜ`
2. `rw [Set.preimage_inter]` — distribute preimage over `∩`
3. `rw [Set.preimage_compl]` — distribute preimage over `ᶜ`
4. `rw [Set.diff_eq]` — rewrite `∩ ... ᶜ` back to `\\`

Each step uses a result you proved earlier in this world. Instead
of reproving from scratch, you are **composing** your library.
This is how mathematics really works.
"

/-- Preimage distributes over set difference. -/
Statement (α β : Type) (f : α → β) (s t : Set β) :
    f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := by
  Hint "Start by rewriting set difference as intersection with
  complement: `rw [Set.diff_eq]`.

  This uses the theorem `Set.diff_eq : s \\ t = s ∩ tᶜ` to convert
  the `\\` on the left side into `∩` and `ᶜ`."
  Hint (hidden := true) "The full proof is:
  `rw [Set.diff_eq]`
  `rw [Set.preimage_inter]`
  `rw [Set.preimage_compl]`
  `rw [Set.diff_eq]`"
  rw [Set.diff_eq]
  Hint "Good! The left side now has `f ⁻¹' (s ∩ tᶜ)`. You proved
  that preimage distributes over intersection (Level 8).
  Use `rw [Set.preimage_inter]` to distribute."
  Hint (hidden := true) "`rw [Set.preimage_inter]`"
  rw [Set.preimage_inter]
  Hint "Now the left side has `f ⁻¹' tᶜ`. You proved that preimage
  distributes over complement (Level 10).
  Use `rw [Set.preimage_compl]` to distribute."
  Hint (hidden := true) "`rw [Set.preimage_compl]`"
  rw [Set.preimage_compl]
  Hint "Almost done! The left side is `f ⁻¹' s ∩ (f ⁻¹' t)ᶜ` and
  the right side is `f ⁻¹' s \\ f ⁻¹' t`. Since `s \\ t = s ∩ tᶜ`,
  one more `rw [Set.diff_eq]` converts the right side to match."
  Hint (hidden := true) "`rw [Set.diff_eq]`"
  rw [Set.diff_eq]

Conclusion "
Congratulations — you completed **Preimage World** by composing
your library of results!

The proof was just four rewrites:
1. `rw [Set.diff_eq]` — difference is intersection with complement
2. `rw [Set.preimage_inter]` — preimage distributes over `∩`
3. `rw [Set.preimage_compl]` — preimage distributes over `ᶜ`
4. `rw [Set.diff_eq]` — repackage as difference

No `ext`, no `constructor`, no case analysis. You used previously
proved theorems as building blocks. This is the payoff of having
a library: each new result becomes easier because you can stand on
your earlier work.

## The Complete Preimage Library

You have built a complete theory. Here is everything you proved,
in one place:

| Level | Identity | Logic | Library name |
|---|---|---|---|
| L05 | `s ⊆ t → f ⁻¹' s ⊆ f ⁻¹' t` | monotonicity | `Set.preimage_mono` |
| L06 | `f ⁻¹' ∅ = ∅` | `False` | `Set.preimage_empty` |
| L07 | `f ⁻¹' Set.univ = Set.univ` | `True` | `Set.preimage_univ` |
| L08 | `f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t` | `∧` | `Set.preimage_inter` |
| L09 | `f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t` | `∨` | `Set.preimage_union` |
| L10 | `f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ` | `¬` | `Set.preimage_compl` |
| L11 | `f ⁻¹' (⋃ i, s i) = ⋃ i, f ⁻¹' (s i)` | `∃` | `preimage_iUnion` |
| L12 | `f ⁻¹' (⋂ i, s i) = ⋂ i, f ⁻¹' (s i)` | `∀` | `preimage_iInter` |
| L13 | `id ⁻¹' s = s` | identity | `Set.preimage_id` |
| L14 | `(g . f) ⁻¹' t = f ⁻¹' (g ⁻¹' t)` | composition | `Set.preimage_comp` |
| L16 | `f ⁻¹' (s \\ t) = f ⁻¹' s \\ f ⁻¹' t` | `∧` + `¬` | `Set.preimage_diff` |

Every row says the same thing: **preimage is a Boolean algebra
homomorphism**. It maps the Boolean algebra of subsets of `β`
(with `∩`, `∪`, `ᶜ`, `∅`, `Set.univ`) into the Boolean algebra
of subsets of `α`, preserving all operations. It is also
**contravariant** — it reverses the direction of function
composition (L14).

The single structural reason: preimage is just composition on the
predicate level. `x ∈ f ⁻¹' t` is `(t . f) x`. Composing with
`f` does not change the logical connectives inside `t`.

**The topology connection**: In topology, a function `f` is defined
to be **continuous** if and only if the preimage of every open set
is open. The preservation results you proved here are exactly why
this definition works — continuous functions automatically preserve
all the set-theoretic structure that topology needs.

**Looking ahead**: In Image World, you will study `f '' s` —
the image of a set under a function. Image involves an existential
(`y ∈ f '' s ↔ ∃ x ∈ s, f x = y`), and existentials do NOT
commute with conjunction or negation. Image only preserves union,
not intersection or complement. The contrast between the
well-behaved preimage and the less-well-behaved image is one of
the central themes of this course.
"

/-- `Set.preimage_diff` states `f ⁻¹' (s \\ t) = f ⁻¹' s \\ f ⁻¹' t`. -/
TheoremDoc Set.preimage_diff as "Set.preimage_diff" in "Set"

NewTheorem Set.preimage_diff

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith rfl ext funext
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.preimage_diff Iff.rfl
