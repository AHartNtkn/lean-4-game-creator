# Coverage Map: Functions & Relations

Course scope: Sets as predicates, images/preimages, restriction to subsets,
injective/surjective/bijective maps (global and on-set), relations as sets of pairs,
bundled equivalences and partial equivalences, subtypes, quotients, equivalence
relations and partitions, countable sets, and encodable types. This is the
"language course" for modern mathlib.

Prerequisite: NNG4-level Lean fluency (`rw`, `exact`, `apply`, `intro`, `induction`, etc.).

---

## 1. Coverage Matrix Summary

### MATH axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| `Set α` — sets as predicates `α → Prop` | core | I S R G T | Foundation for everything; must connect to `setOf` and `{x \| p x}` |
| `Set.mem` / `∈` — membership | core | I S R G | Unfolding `x ∈ {y \| p y}` to `p x` is the first move |
| `Set.subset` / `⊆` — subset relation | core | I S R G T | `∀ x, x ∈ s → x ∈ t`; must be drilled before set operations |
| `Set.empty` / `∅` and `Set.univ` | core | I S R G W | Boundary cases; `∅ ⊆ s` and `s ⊆ univ` as tautologies |
| `setOf` — set comprehension `{x \| p x}` | core | I S R G | Builder notation, identical to `Set α` unfolding |
| `Set.union` / `∪`, `Set.inter` / `∩` | core | I S R G T | Connected to `∨` and `∧` on membership |
| `Set.compl` / `sᶜ`, `Set.diff` / `s \ t` | core | I S R G T | Connected to `¬` and `∧ ¬` on membership |
| `Set.powerset` | supporting | I S R | `𝒫 s = {t \| t ⊆ s}` |
| `Set.prod` / `s ×ˢ t` — cartesian product | core | I S R G | Product of sets; membership is `∧` |
| `Set.diagonal` — `{(x, x) \| x}` | supporting | I S R | Relations live in `Set (α × α)`; diagonal = equality relation |
| `Set.offDiag` | optional | I S | Strict inequality pairs |
| `Set.image` / `f '' s` | core | I S R G T | Forward image; `y ∈ f '' s ↔ ∃ x ∈ s, f x = y` |
| `Set.preimage` / `f ⁻¹' t` | core | I S R G T | Inverse image; `x ∈ f ⁻¹' t ↔ f x ∈ t` |
| `Set.range` / `Set.range f` | core | I S R G | Image of `univ`; range of a function |
| `Set.image` / `Set.preimage` Galois connection | core | I S R G | `image_subset_iff : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t` |
| `Set.iUnion` / `⋃ i, s i`, `Set.iInter` / `⋂ i, s i` | core | I S R G | Indexed union/intersection; existential/universal on membership |
| Bounded `⋃ i ∈ s, f i` / `⋂ i ∈ s, f i` (`iUnion₂`/`iInter₂`) | core | I S R G | Bounded indexed union/intersection; `mem_iUnion₂`, `mem_iInter₂` |
| `Set.sUnion` / `⋃₀ S`, `Set.sInter` / `⋂₀ S` | supporting | I S R | Union/intersection of a set of sets |
| `Set.Nonempty` | core | I S R G | `∃ x, x ∈ s`; preferred over `s ≠ ∅` |
| `Set.Subsingleton` / `Set.Nontrivial` | supporting | I S | At-most-one / at-least-two elements |
| `Set.encard` / `Set.ncard` — set cardinality | supporting | I S R | `encard` in `ℕ∞`, `ncard` in `ℕ` (0 for infinite) |
| `Function.Injective` | core | I S R G T | `∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂` |
| `Function.Surjective` | core | I S R G T | `∀ b, ∃ a, f a = b` |
| `Function.Bijective` | core | I S R G T | Injective ∧ Surjective |
| `Function.Embedding` / `α ↪ β` | supporting | I S R | Bundled injection; intermediate between `Injective` predicate and `Equiv` structure |
| `Function.LeftInverse` / `Function.RightInverse` | core | I S R G | `g ∘ f = id` / `f ∘ g = id` |
| `Function.Involutive` | supporting | I S | `f ∘ f = id` |
| Cantor's theorem / `Function.cantor_surjective` | core | I S R T | No surjection `α → Set α` (`(f : α → Set α) → ¬Surjective f`); capstone-worthy |
| Cantor's theorem / `Function.cantor_injective` | core | I S R T | No injection `Set α → α` (`(f : Set α → α) → ¬Injective f`); dual of surjective version |
| `Set.MapsTo f s t` | core | I S R G | `∀ x ∈ s, f x ∈ t` |
| `Set.InjOn f s` | core | I S R G | Injectivity restricted to a set |
| `Set.SurjOn f s t` | core | I S R G | Surjectivity restricted to sets |
| `Set.BijOn f s t` | core | I S R G | Bijection between sets; combines `MapsTo`, `InjOn`, `SurjOn` |
| `Set.EqOn f g s` | supporting | I S R | Equality of functions on a set |
| `Set.LeftInvOn` / `Set.RightInvOn` / `Set.InvOn` | supporting | I S R | Inverse relations on restricted domains |
| `Set.restrict f s` | supporting | I S R | Restricting function domain to a set |
| `invFunOn` — constructing inverses on sets | supporting | I S R | Noncomputable inverse on a set |
| Binary relation as `Set (α × α)` or `α → α → Prop` | core | I S R G T | Two representations; must connect both |
| Reflexive / Symmetric / Transitive (unbundled) | core | I S R G | Properties of relations |
| `Equivalence` — bundled refl+symm+trans | core | I S R G T | The bridge to Setoid |
| `Setoid α` — equivalence relation typeclass | core | I S R G T | Bundled equivalence relation |
| `Setoid.ker f` — kernel of a function | core | I S R G | `x ≈ y ↔ f x = f y`; fundamental example |
| `Quotient` / `Quotient.mk` / `Quotient.lift` | core | I S R G T | Quotient type; lifting functions through quotients |
| `Quotient.sound` / `Quotient.exact` | core | I S R G | Going between `≈` and `=` in quotient |
| `Quotient.map` | supporting | I S R | Maps between quotient types; defines functions `Quotient sa → Quotient sb` |
| `Quotient.out` | supporting | I S R | Extracts a canonical representative from a quotient element |
| Equivalence classes / `Setoid.classes` | core | I S R G | The set of equivalence classes |
| `Setoid.IsPartition` | core | I S R G T | Partition ↔ equivalence relation correspondence |
| `IndexedPartition` | supporting | I S | Constructive partitions with index function |
| Partition–equivalence-relation bijection | core | I S R G T | `Setoid.Partition.orderIso`; the fundamental theorem |
| `Setoid.quotientKerEquivRange` — first isomorphism theorem for setoids | core | I S R G | `Quotient (ker f) ≃ ↑(Set.range f)`; bridges quotient world to function world |
| `Setoid.quotientKerEquivOfSurjective` — quotient of surjection | supporting | I S R | `Quotient (ker f) ≃ β` when `f` is surjective; special case of above |
| `Setoid.quotientEquivClasses` — quotient ≃ equivalence classes | supporting | I S R | `Quotient r ≃ ↑r.classes`; completes partition↔equivalence at the type-equivalence level |
| `Subtype` — `{x : α // p x}` | core | I S R G T | Types from predicates; ↥s coercion from sets |
| `↥s` — coercion from `Set α` to `Type` | core | I S R G W | `Set α` coerces to subtype; heavy notation burden |
| `Subtype.val` / `Subtype.coe` | core | I S R G | Extracting the underlying element |
| `Subtype.mk` | core | I S R | Constructing subtype elements with proof |
| `Equiv α β` — bundled equivalence `α ≃ β` | core | I S R G T | Bijection as a structure |
| `Equiv.refl` / `Equiv.symm` / `Equiv.trans` | core | I S R G | Group-like operations on equivalences |
| `Equiv.toFun` / `Equiv.invFun` | core | I S R G | Forward and inverse maps |
| `Equiv.ofBijective` | core | I S R G | Constructing `Equiv` from a bijective function |
| `Equiv.ofInjective` | supporting | I S R | Domain ≃ range for injective functions |
| `Equiv.Set.univ` / `Equiv.Set.union` / `Equiv.Set.sumCompl` | supporting | I S R | Set-type equivalences |
| `Equiv.subtypeEquiv` | supporting | I S | Equivalent predicates give equivalent subtypes |
| `PartialEquiv α β` — local equivalences | supporting | I S R | Bijection between subsets; source and target |
| `Countable α` | core | I S R G T | `∃ f : α → ℕ, Injective f` |
| `Encodable α` | core | I S R G | Constructive countability with encode/decode |
| `Denumerable α` | core | I S R G | Constructively bijective with ℕ; `α ≃ ℕ` |
| `Set.Countable` | core | I S R G | `Countable ↥s`; countability of a set |
| Countability of ℕ, ℤ, ℚ | core | I S R | Standard instances |
| Countability of products, sums, subtypes, quotients | core | I S R G | Closure under type constructors |
| `Set.Countable` closure: unions, images, subsets | core | I S R G | Countable sets are closed under standard operations |
| Uncountability of ℝ / `Set α` | core | I S R T | Cantor-style diagonal; capstone |
| `Encodable.encode` / `Encodable.decode` | core | I S R | The constructive interface |
| `Denumerable.eqv` — `α ≃ ℕ` from `Denumerable` | supporting | I S R | Explicit equivalence |
| `Encodable` instances for Option, Sum, Prod, Sigma | supporting | I S R | How encodability composes |

### MOVE axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| Unfold a set membership to its predicate definition | core | I S R G | `x ∈ {y \| p y}` becomes `p x` |
| Prove subset by `intro x hx` then show membership | core | I S R G T | The universal proof shape for `⊆` |
| Prove set equality by `ext x` (double containment) | core | I S R G T | `s = t ↔ ∀ x, x ∈ s ↔ x ∈ t` |
| Prove nonemptiness by exhibiting a witness | core | I S R G | `⟨x, hx⟩` for `Set.Nonempty` |
| Prove image membership by exhibiting a preimage | core | I S R G T | `⟨x, hxs, rfl⟩` for `y ∈ f '' s` |
| Prove preimage membership by applying function | core | I S R G | Direct computation for `x ∈ f ⁻¹' t` |
| Prove injectivity by assuming `f a = f b` and deriving `a = b` | core | I S R G T | The canonical proof shape |
| Prove surjectivity by producing a preimage for arbitrary `b` | core | I S R G T | The canonical proof shape |
| Compose injectivity/surjectivity through composition | core | I S R G | `Injective g → Injective f → Injective (g ∘ f)` etc. |
| Extract injectivity/surjectivity from composition | core | I S R G | `Injective (g ∘ f) → Injective f` etc. |
| Construct left/right inverse to prove injective/surjective | core | I S R G T | The inverse-based proof strategy |
| Prove equivalence relation by checking three properties | core | I S R G T | Refl + symm + trans |
| Define a quotient and lift a function through it | core | I S R G | `Quotient.lift f h` with well-definedness proof |
| Prove well-definedness for quotient lifting | core | I S R G T | The obligation: `a ≈ b → f a = f b` |
| Construct a subtype element with proof | core | I S R G | `⟨x, proof⟩ : {x // p x}` |
| Use subtype coercion to access the underlying element | core | I S R G | `(a : α)` from `a : ↥s` |
| Build an `Equiv` from forward/inverse maps | core | I S R G | Supply `toFun`, `invFun`, `left_inv`, `right_inv` |
| Prove two `Equiv`s compose correctly | supporting | I S R | `Equiv.trans` |
| Diagonal argument: assume surjection, derive contradiction | core | I S R T | Cantor's proof shape |
| Prove countability by constructing an injection to ℕ | core | I S R G | The definition-unfolding proof |
| Prove countability by constructing a surjection from ℕ | supporting | I S R | Alternative characterization |
| Transfer countability through images/subsets/unions | core | I S R G | Closure proofs |
| Prove uncountability by contradiction + diagonal | core | I S R T | Cantor on `ℕ → Bool` or `Set ℕ` |
| Build an `Encodable` instance via encode/decode pair | supporting | I S R | The constructive proof |
| Prove a partition gives an equivalence relation | core | I S R G T | The correspondence proof |
| Prove an equivalence relation gives a partition | core | I S R G T | The other direction |

### LEAN axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| `ext` — extensionality for sets and functions | core | I S R G | `Set.ext`, `funext` |
| `simp` with set-theory simp lemmas | core | I S R G | `mem_union`, `mem_inter`, `mem_compl`, etc. (when not disabled) |
| `constructor` for `↔` goals | core | I S R G | Splitting biconditionals |
| `obtain ⟨x, hx⟩` — destructuring existentials | core | I S R G | Extracting witnesses |
| `use` — providing existential witnesses | core | I S R G | For `∃` goals |
| `rintro` with anonymous constructors | core | I S R G | Pattern-matching intro |
| `rcases` for deep pattern matching | core | I S R G | Destructuring complex hypotheses |
| `change` — rewriting goal to definitionally equal form | supporting | I S R | Useful for unfolding set membership |
| `show` — stating what you're about to prove | supporting | I S R | Clarifying the goal |
| `push_neg` — pushing negation through quantifiers | core | I S R G | Essential for complement/emptiness proofs |
| `by_contra` / `by_contradiction` | core | I S R G | Contradiction-based proofs |
| `Quotient.inductionOn` | core | I S R G | Induction on quotient representatives |
| `Subtype.ext` | supporting | I S R | Equality of subtype elements |
| `exact?` / `apply?` — search tactics | supporting | I S | Finding the right lemma (when available) |
| `calc` blocks for chains of equalities/subset relations | supporting | I S R | Readable proof structure |
| `congr` — congruence | supporting | I S R | For matching structural goals |
| `tauto` — propositional tautology solver | supporting | I S R | For pure logic steps (when not disabled) |
| `Set.eq_empty_iff_forall_not_mem` | supporting | I S R | Characterizing emptiness |
| `Set.nonempty_iff_ne_empty` | supporting | I S R | Connecting nonemptiness representations |

### NOTATION axis

| Item | Importance | Planned stages | Notes |
|------|-----------|---------------|-------|
| `{x \| p x}` and `{x : α \| p x}` — set builder notation | core | I S R G W | Two forms; type annotation sometimes needed |
| `∈` and `∉` for set membership | core | I S R G | Basic; but `∉` is `¬ ∈` which needs `push_neg` |
| `⊆` and `⊂` for subset | core | I S R G | `⊂` is strict, rarely needed early |
| `∪`, `∩`, `\`, `ᶜ` — set operations | core | I S R G | Backslash is `sdiff`, `ᶜ` is complement |
| `f '' s` — image notation | core | I S R G W | Double-prime; NOT `f(s)` or `f ' s` |
| `f ⁻¹' t` — preimage notation | core | I S R G W | Superscript-minus-one-prime; fragile to type |
| `⋃ i, s i` and `⋂ i, s i` — indexed union/intersection | core | I S R G | Binder notation |
| `⋃₀ S` and `⋂₀ S` — set union/intersection | supporting | I S R | Subscript-zero notation |
| `s ×ˢ t` — set product | core | I S R | Superscript-s after ×; not standard `×` |
| `↥s` — coercion from `Set α` to `Type` | core | I S R G W | Arrow-up; a major confusion point |
| `(a : α)` from `a : ↥s` — coercion down | core | I S R G | Implicit vs explicit coercion |
| `α ≃ β` — `Equiv` notation | core | I S R G | Tilde-equals; not `=` or `≅` |
| `⟨_, _⟩` — anonymous constructor for subtypes | core | I S R G | Angle brackets |
| `Quotient.mk'` vs `Quotient.mk` | supporting | I S W | Primed vs unprimed; API choice |
| `≈` — setoid equivalence | core | I S R G | Not `=`; learners will confuse these |
| `Set.range f` vs `f '' Set.univ` | supporting | I S W | Two ways to say the same thing |

### MISCONCEPTION axis

| Item | Importance | Context | Notes |
|------|-----------|---------|-------|
| Sets are not types; `x ∈ s` is `Prop`, not a type judgment | core | W at introduction | The #1 confusion from set theory courses |
| `↥s` coercion silently changes the type context | core | W at Subtype intro | Learners won't understand why terms have different types |
| Image ≠ preimage for inclusions: `f '' (f ⁻¹' t) ⊆ t` but equality needs surjectivity | core | W at image/preimage | Learners expect equality |
| `f ⁻¹' (f '' s) ⊇ s` but equality needs injectivity | core | W at image/preimage | The dual trap |
| Intersection of images ⊇ image of intersection; equality needs injectivity | core | W at set operations | `f '' (s ∩ t) ⊆ f '' s ∩ f '' t` is only ⊆ |
| `Set.prod` uses `×ˢ`, not `×`; membership is `∧` | supporting | W at products | Notation collision |
| `Equiv` is data (forward + inverse + proofs); it is not just "bijectivity" | core | W at Equiv | Learners think `Bijective f` = `Equiv` |
| Quotient lifting requires well-definedness proof; this is not optional | core | W at quotient | Learners try to `exact` without the obligation |
| `Countable` is nonconstructive; `Encodable` is constructive | supporting | W at countability | Different proof obligations |
| `Denumerable` is stronger than `Encodable` (requires surjectivity of decode) | supporting | W at countability | "Every ℕ maps to something" vs "some ℕ maps to something" |
| Cantor's theorem: there is no surjection `α → Set α`; learners may confuse with uncountability of ℝ | core | W at Cantor | These are related but distinct results |
| Equivalence relation ≠ equality; `≈` and `=` are different things | core | W at Setoid | The foundational distinction of the course |
| A partition has no empty parts; learners forget this condition | supporting | W at partitions | `IsPartition` excludes `∅` |
| `InjOn f s` is weaker than `Injective f`; they are not interchangeable | core | W at on-set maps | The whole point of restricted maps |
| `BijOn f s t` requires three separate proofs; it's not `BijOn = InjOn ∧ SurjOn` alone (needs `MapsTo`) | supporting | W at on-set maps | Learners miss the `MapsTo` component |
| Complement is not the same as difference: `sᶜ = univ \ s` | supporting | W at set operations | Notation confusion |

### TRANSFER axis

| Item | Importance | Notes |
|------|-----------|-------|
| "To show two sets are equal, show each is contained in the other" | core | Double-containment is the universal strategy |
| "To show something is in an image, find what maps to it" | core | Witness production |
| "To show a function is injective, assume equal outputs and derive equal inputs" | core | The standard proof template |
| "To show a function is surjective, take an arbitrary element and find its preimage" | core | The standard proof template |
| "An equivalence relation partitions a set; a partition defines an equivalence relation" | core | The fundamental correspondence |
| "A quotient collapses equivalent elements to single points" | core | Geometric/visual intuition |
| "Well-definedness means the answer doesn't depend on the representative" | core | The quotient obligation in plain language |
| "Countable means you can list everything (possibly with repetition)" | core | Surjection from ℕ characterization |
| "Uncountable means no listing is possible — something always gets missed" | core | Cantor's insight in words |
| "An equivalence (Equiv) is a perfect matching between two types" | core | Bijection with data |
| "Three notions of sameness: `=` (identical), `≈` (equivalent under a relation), `≃` (bijection with data)" | core | The fundamental three-way distinction this course teaches; must be drawn explicitly as a teaching moment, not left implicit |
| "Preimage preserves all set operations; image only preserves unions" | supporting | The asymmetry principle |
| "Restricting to a subset means working with a subtype" | core | The set→type bridge |

### EXAMPLE axis

| Item | Role | Notes |
|------|------|-------|
| `{n : ℕ \| n < 5}` — a finite set defined by a predicate | concretization | First example of `Set`; learners can compute membership |
| `{n : ℕ \| Even n}` — the even naturals | concretization | Infinite set; preimage of `{0}` under `n % 2` |
| `Set.univ (α := Fin 3)` — a small universal set | concretization | Everything in a small type |
| `fun n : ℕ => 2 * n` — doubling as injective, not surjective | concretization + counterexample | Injective but not surjective; concrete and computable |
| `fun n : ℕ => n / 2` — halving as surjective, not injective | concretization + counterexample | Surjective but not injective |
| `fun n : ℕ => n + 1` — successor as injective, not surjective | concretization | Alternative injective non-surjection |
| `id` on any type — bijective | concretization | Trivial bijection |
| `fun (a, b) : ℕ × ℕ => a + b` — not injective | counterexample | Kernel has nontrivial equivalence classes |
| Equivalence relation: `n ≡ m [MOD k]` — congruence mod k | concretization | The canonical equivalence relation |
| Equivalence relation: same-parity on ℕ | concretization | Simplest nontrivial example (2 classes) |
| Non-equivalence: `a ≤ b` on ℕ | counterexample | Reflexive, transitive, but not symmetric |
| Non-equivalence: `a ≠ b` on ℕ | counterexample | Symmetric but not reflexive or transitive |
| `ℤ` modulo 3 — quotient `ℤ / 3ℤ` | concretization | Concrete quotient type with 3 classes |
| `ℕ × ℕ` quotiented by `(a,b) ≈ (c,d) ↔ a + d = b + c` — constructing ℤ | concretization + integration | Major example: building integers from naturals |
| `Equiv.refl ℕ` — identity equivalence | concretization | Trivial Equiv |
| `Equiv` between `Fin 2` and `Bool` | concretization | Small concrete equivalence |
| `Equiv` between `ℕ` and `ℕ × ℕ` (pairing function) | concretization + integration | Denumerable instance; Cantor pairing |
| `Set.range (fun n : ℕ => 2 * n)` — the even naturals as a range | concretization | Connects range and image |
| `Nat.succ` as a function `ℕ → ℕ` — image is `{n \| n ≥ 1}`, preimage of `{0}` is `∅` | concretization | Image/preimage worked example |
| `Set ℕ` — the powerset of ℕ | concretization | Uncountable set; Cantor's theorem target |
| `ℕ → Bool` — binary sequences | concretization | Alternative target for diagonalization |
| `ℚ` as countable, `ℝ` as uncountable | concretization + contrast | The big picture |
| Partition of ℤ into even/odd | concretization | Simplest nontrivial partition |
| Partition of ℕ into residue classes mod 3 | concretization | 3-class partition |
| `{x : ℕ // x > 0}` — positive naturals as subtype | concretization | Concrete subtype |
| `↥({n : ℕ \| Even n})` — even naturals as a type | concretization | Set-to-type coercion in action |
| `PartialEquiv` between `{n : ℕ // n > 0}` and `ℕ` via `n ↦ n - 1` / `m ↦ m + 1` | concretization | Concrete `PartialEquiv` with explicit source/target and partial inverse |
| `⋃ k ∈ Finset.range 3, {n : ℕ \| n % 3 = k}` = `Set.univ` | concretization | Bounded indexed union recovering the whole type |
| `f : ℤ → ZMod 3` with `Setoid.ker f` — first isomorphism theorem | concretization + integration | Kernel → quotient → range equivalence made concrete |

---

## 2. Core Items That Must Not Be Missed

These items define what it means to have taken this course. If any is missing, the course fails.

### Sets
1. **Set as predicate**: `Set α = α → Prop`. The learner must internalize that set membership is proposition evaluation.
2. **Subset as universal implication**: `s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t`.
3. **Set extensionality**: `s = t ↔ ∀ x, x ∈ s ↔ x ∈ t`. The primary proof technique.
4. **Set operations reduce to logic**: `∪` ↔ `∨`, `∩` ↔ `∧`, `ᶜ` ↔ `¬`. This is the entire point.
5. **Image and preimage** as the function–set interface, with their asymmetry (preimage preserves all operations; image only preserves unions).

### Functions
6. **Injective/Surjective/Bijective** as global predicates with their canonical proof shapes.
7. **On-set variants**: `MapsTo`, `InjOn`, `SurjOn`, `BijOn` as restrictions — and why they matter.
8. **Composition laws**: how injectivity/surjectivity compose and what can be extracted from composite injectivity/surjectivity.
9. **Left/right inverse** characterizations of injective/surjective functions.

### Relations and equivalences
10. **Relation as predicate or as subset of product**: both representations.
11. **Equivalence relation**: reflexive + symmetric + transitive, checked individually.
12. **Setoid and Quotient**: bundled equivalence relation → quotient type → lifting functions.
13. **Well-definedness obligation**: the key proof obligation when lifting through quotients.
14. **Partition ↔ equivalence relation correspondence**: the fundamental theorem.

### Types and encodability
15. **Subtype**: `{x : α // p x}`, construction, coercion, the `↥s` notation.
16. **Equiv**: bundled bijection with data (forward, inverse, proofs), not just bijectivity.
17. **Countable / Encodable / Denumerable**: the three levels of constructive countability.
18. **Cantor's theorem**: no surjection `α → Set α`; the diagonal argument.
19. **Countability closure**: under images, subsets, countable unions.

---

## 3. Example Plan

### Sets and membership
- **Concrete set**: `{n : ℕ | n < 5}` — first example, computable membership.
- **Infinite set**: `{n : ℕ | Even n}` — shows sets need not be finite.
- **Empty set**: `{n : ℕ | n < 0}` = `∅` — boundary case.
- **Universal set**: `Set.univ` on `Fin 3` — small, exhaustible.

### Set operations
- **Union**: `{n | n < 3} ∪ {n | n > 5}` — disjoint pieces.
- **Intersection**: `{n | Even n} ∩ {n | n < 10}` — finite intersection of infinite set with predicate.
- **Complement**: `{n : ℕ | Even n}ᶜ = {n | ¬ Even n}` — odd naturals.
- **Difference**: `{n | n < 10} \ {n | Even n}` — odd numbers less than 10.
- **Counterexample for union ≠ disjoint union**: `{1,2,3} ∪ {2,3,4}` shares elements.
- **De Morgan**: `({n | Even n} ∪ {n | n < 5})ᶜ = {n | ¬ Even n} ∩ {n | n ≥ 5}` — integration exercise combining `ext`, complement, `push_neg`.
- **Bounded indexed union**: `⋃ k ∈ Finset.range 3, {n : ℕ | n % 3 = k}` = `Set.univ` — shows how bounded unions cover a type.

### Image and preimage
- **Image**: `(fun n => 2*n) '' {0, 1, 2, 3}` = `{0, 2, 4, 6}`.
- **Preimage**: `(fun n => n % 2) ⁻¹' {0}` = `{n | Even n}`.
- **Image–preimage gap**: `f '' (f ⁻¹' t) ⊊ t` when f not surjective (e.g., `Nat.succ` and `{0, 1}`).
- **Preimage–image gap**: `f ⁻¹' (f '' s) ⊋ s` when f not injective (e.g., `fun n => n/2` and `{1}`).

### Functions
- **Injective, not surjective**: `fun n : ℕ => 2 * n`.
- **Surjective, not injective**: `fun n : ℕ => n / 2`.
- **Bijective**: `fun n : ℤ => n + 1` (or `id`).
- **Neither**: `fun _ : ℕ => 0` (constant function on ℕ with `|ℕ| > 1`).
- **Counterexample for "injective composition → components injective"**: `g ∘ f` injective implies `f` injective but NOT `g` injective.

### Relations
- **Equivalence**: `n ≡ m [MOD 3]` on ℤ — canonical, 3 classes.
- **Equivalence**: same parity on ℕ — simplest nontrivial, 2 classes.
- **Not symmetric**: `≤` on ℕ — reflexive and transitive but not symmetric.
- **Not transitive**: "differs by exactly 1" on ℤ — symmetric and reflexive on adjacent integers but not transitive.
- **Not reflexive**: `≠` on ℕ — symmetric and (vacuously on pairs where it applies) but not reflexive.

### Quotients and partitions
- **ℤ mod 3**: concrete quotient with 3 equivalence classes.
- **ℤ from ℕ × ℕ**: `(a,b) ≈ (c,d) ↔ a + d = b + c` — motivating quotient construction.
- **Partition**: ℤ into `{..., -3, 0, 3, 6, ...}`, `{..., -2, 1, 4, 7, ...}`, `{..., -1, 2, 5, 8, ...}`.
- **Not a partition**: `{{1,2}, {2,3}, {4}}` of `{1,2,3,4}` — overlapping parts.
- **Not a partition**: `{{1,2}, ∅, {3}}` — empty part violates definition.

### Kernel→quotient→range
- **First isomorphism theorem**: `f : ℤ → ZMod 3` — `Setoid.ker f` produces the mod-3 equivalence relation, and `quotientKerEquivRange` gives `Quotient (ker f) ≃ ↑(Set.range f)` ≃ `ZMod 3`. Makes the abstract theorem concrete.
- **Surjective specialization**: same `f : ℤ → ZMod 3` is surjective, so `quotientKerEquivOfSurjective` gives `Quotient (ker f) ≃ ZMod 3` directly.

### Subtypes, Equiv, and PartialEquiv
- **Subtype**: `{x : ℕ // x > 0}` — positive naturals.
- **Equiv**: `Fin 2 ≃ Bool` — small, concrete, computable.
- **Equiv**: `ℕ ≃ ℕ × ℕ` via Cantor pairing — nontrivial, relates to countability.
- **Non-Equiv**: no `ℕ ≃ Set ℕ` — Cantor's theorem.
- **PartialEquiv**: `{n : ℕ // n > 0} ↔ ℕ` via `n ↦ n - 1` / `m ↦ m + 1` — bijection between positive naturals and all naturals, with explicit source and target sets.

### Countability
- **Countable**: ℕ, ℤ, ℚ, `ℕ × ℕ`.
- **Uncountable**: `Set ℕ`, `ℕ → Bool`, ℝ.
- **Countable set**: `{n : ℕ | Even n}` — countable subset of countable type.
- **Countable union**: `⋃ k, {n : ℕ | n ≡ k [MOD 3]}` for `k ∈ Fin 3` — union of countable sets.

---

## 4. Proof-Move Clusters

These are groups of related proof moves that should be taught together (or in close sequence) because they share a common proof shape or reinforce each other.

### Cluster 1: Set membership and logic
- Unfold `x ∈ {y | p y}` to `p x`
- Unfold `x ∈ s ∪ t` to `x ∈ s ∨ x ∈ t` (and similarly for ∩, ᶜ)
- Use `left`/`right` for union membership
- Use `constructor` or `⟨_, _⟩` for intersection membership
- Use `push_neg` for complement and emptiness

This cluster is the foundation. Every later cluster uses it.

### Cluster 2: Subset and set equality
- Prove `s ⊆ t` by `intro x hx` then derive `x ∈ t`
- Prove `s = t` by `ext x` then prove `↔`
- Chain subset steps for transitivity
- Prove `s = ∅` via `eq_empty_iff_forall_not_mem`

### Cluster 3: Image and preimage manipulation
- Prove `y ∈ f '' s` by `⟨x, hx, rfl⟩`
- Prove `x ∈ f ⁻¹' t` by showing `f x ∈ t`
- Prove `f '' s ⊆ t` by taking `y ∈ f '' s`, obtaining `⟨x, hx, hfx⟩`, then showing `y ∈ t`
- Use `image_subset_iff` to switch to preimage
- Prove `image_union`, `preimage_inter`, etc. by membership unfolding

### Cluster 4: Injectivity and surjectivity proofs
- Prove `Injective f` by `intro a b hab` then derive `a = b`
- Prove `Surjective f` by `intro b` then `use` a witness
- Prove `Bijective f` by `constructor` then prove each half
- Compose: `Injective g → Injective f → Injective (g ∘ f)`
- Extract: `Injective (g ∘ f) → Injective f`
- Left inverse → injective; right inverse → surjective

### Cluster 5: On-set function properties
- Prove `MapsTo f s t` by `intro x hx` then show `f x ∈ t`
- Prove `InjOn f s` by `intro a ha b hb hab` then derive `a = b`
- Prove `SurjOn f s t` by `intro y hy` then produce `⟨x, hx, hfx⟩`
- Prove `BijOn f s t` by proving `MapsTo`, `InjOn`, `SurjOn` separately
- Connect `InjOn f univ ↔ Injective f` (and similarly for others)

### Cluster 6: Relation properties
- Check reflexivity: `intro x` then prove `R x x`
- Check symmetry: `intro x y hxy` then prove `R y x`
- Check transitivity: `intro x y z hxy hyz` then prove `R x z`
- Bundle into `Equivalence` structure
- Construct `Setoid` from `Equivalence`

### Cluster 7: Quotient construction and use
- Construct `Quotient.mk' a` for an element
- Prove `Quotient.sound` from `a ≈ b` to `⟦a⟧ = ⟦b⟧`
- Prove `Quotient.exact` from `⟦a⟧ = ⟦b⟧` to `a ≈ b`
- Lift a function: define `f` on representatives, prove well-definedness, apply `Quotient.lift`
- Induction on quotients: `Quotient.inductionOn`
- Map between quotients: `Quotient.map` with proof that the function respects both equivalence relations
- Extract representative: `Quotient.out` (noncomputable; use with care)

### Cluster 7b: Indexed union/intersection proof moves
- Prove `x ∈ ⋃ i, s i` by `rw [Set.mem_iUnion]` then `use` a witness index (existential pattern)
- Prove `x ∈ ⋂ i, s i` by `rw [Set.mem_iInter]` then `intro i` (universal pattern)
- Bounded variant: `x ∈ ⋃ i ∈ t, s i` unfolds via `mem_iUnion₂` to `∃ i, ∃ _ : i ∈ t, x ∈ s i`
- Bounded variant: `x ∈ ⋂ i ∈ t, s i` unfolds via `mem_iInter₂` to `∀ i, i ∈ t → x ∈ s i`
- Contrast with binary union: `∪` uses `left`/`right`; `⋃` uses `use`/`obtain`

Note: This is a distinct proof shape from binary union/intersection (Cluster 1). Binary operations reduce to `∨`/`∧` and use `left`/`right`/`constructor`. Indexed operations reduce to `∃`/`∀` and use `use`/`intro`.

### Cluster 7c: De Morgan's laws for sets
- `(s ∪ t)ᶜ = sᶜ ∩ tᶜ` — prove by `ext x`, unfold complement and union membership, apply propositional De Morgan
- `(s ∩ t)ᶜ = sᶜ ∪ tᶜ` — same shape, dual direction
- Requires combining `ext`, complement unfolding, `push_neg`, and propositional logic
- Natural integration exercise after Clusters 1 and 2 are established

### Cluster 7d: Kernel→quotient→range (first isomorphism theorem)
- Given `f : α → β`, form `Setoid.ker f` (the kernel setoid: `x ≈ y ↔ f x = f y`)
- Construct the quotient `Quotient (Setoid.ker f)`
- Use `Setoid.kerLift f` to factor `f` through the quotient (`f = kerLift f ∘ Quotient.mk'`)
- Apply `Setoid.quotientKerEquivRange` to get `Quotient (ker f) ≃ ↑(Set.range f)`
- Special case: when `f` is surjective, use `Setoid.quotientKerEquivOfSurjective` for `Quotient (ker f) ≃ β`
- This cluster bridges Cluster 7 (quotient construction) to Cluster 4 (injectivity/surjectivity)

### Cluster 8: Subtype construction and coercion
- Construct `⟨x, proof⟩ : {x // p x}`
- Access value via `Subtype.val` or coercion `(a : α)`
- Prove equality via `Subtype.ext`
- Navigate `↥s` coercion from `Set α`
- Restrict a function to a subtype
- Use `Subtype.coe_injective` — injectivity of the coercion `↥s → α`
- Use `SetCoe.ext` / `SetCoe.ext_iff` — equality of set coercion elements
- Navigate goal states where Lean displays `↑x` vs `(x : α)` vs `x.val` (all equivalent, but confusing)

### Cluster 9: Equiv construction
- Build `Equiv` from `toFun`, `invFun`, `left_inv`, `right_inv`
- Use `Equiv.ofBijective` from a `Bijective` proof
- Compose with `Equiv.trans`
- Invert with `Equiv.symm`
- Connect `Equiv.ofInjective` for domain ≃ range

### Cluster 10: Countability proofs
- Construct injection to ℕ for `Countable`
- Construct encode/decode for `Encodable`
- Use `Denumerable.eqv` for full `α ≃ ℕ`
- Close under products, sums, subtypes
- Transfer through images and subsets
- Diagonal argument for uncountability

---

## 5. Novelty Hotspots

These are places where too much novelty would concentrate without careful sequencing.

### Hotspot 1: First set level
**Risk**: New math (sets as predicates) + new notation (`{x | p x}`, `∈`, `⊆`) + new proof move (unfold membership) arrive simultaneously.
**Mitigation**: Use a mathematically trivial first example (`x ∈ {y | True}` or `x ∈ Set.univ`) so the only new thing is the notation. Build up to `{x | p x}` for nontrivial `p` one step at a time.

### Hotspot 2: Image/preimage introduction
**Risk**: New notation (`f '' s`, `f ⁻¹' t`) + new math (image/preimage definitions) + existential-witness proof move for image membership.
**Mitigation**: Introduce preimage first (it's just function application, which is familiar). Then introduce image, which requires the new witness move. Separate the notation lesson from the proof-move lesson.

### Hotspot 3: Transition from global to on-set function properties
**Risk**: `InjOn`, `SurjOn`, `BijOn`, `MapsTo` are four new definitions at once, plus the universal-to-restricted transfer principle.
**Mitigation**: Introduce `MapsTo` first (it's just subset + function application, both familiar). Then `InjOn` as a restriction of `Injective`. Then `SurjOn`. Only then `BijOn` as the combination.

### Hotspot 4: Quotient introduction
**Risk**: `Setoid` (new type) + `Quotient` (new type) + `Quotient.mk` (new constructor) + `Quotient.lift` (new mechanism) + well-definedness obligation (new proof shape) + `≈` notation (new symbol).
**Mitigation**: Spread across at least 4-5 levels. Introduce `Setoid` on a familiar equivalence relation (mod k). Then `Quotient.mk` and `Quotient.sound`/`exact` on the same example. Then `Quotient.lift` with a simple function. The well-definedness proof is the main new burden — isolate it.

### Hotspot 5: Subtype/coercion notation
**Risk**: `{x // p x}` looks like `{x | p x}` but means something different. `↥s` is new and opaque. Coercion changes type context silently.
**Mitigation**: Explicitly contrast subtype and set notation side-by-side. Have a level where the learner must distinguish them. Introduce `↥s` only after subtypes are comfortable.

### Hotspot 6: Countability hierarchy
**Risk**: `Countable`, `Encodable`, `Denumerable` are three related but distinct concepts introduced in close proximity.
**Mitigation**: Start with `Countable` (simplest: just an injection). Then `Encodable` (adds constructive decode). Then `Denumerable` (adds surjectivity of decode). Each builds on the previous.

---

## 6. Items to Demote, Delay, or Hide

### Delay (teach later in the course, not at the point of conceptual introduction)
- `Set.sUnion` / `Set.sInter` — delay until after `iUnion`/`iInter` are comfortable; they're less common and add notation burden without new proof moves.
- `PartialEquiv` — delay until after `Equiv` is solid; it's a generalization that requires more bookkeeping.
- `Set.encard` / `Set.ncard` — delay until countability section; cardinality is not needed for the set-operations or function-properties portions.
- `IndexedPartition` — delay until after the partition ↔ equivalence correspondence is established with `IsPartition`.
- `Denumerable` — delay until after `Encodable` is comfortable; it's a strictly stronger condition.
- `Function.Involutive` — delay until it appears naturally (e.g., complement-of-complement).
- `Equiv.subtypeEquiv` and other higher `Equiv` constructors — delay until `Equiv` basics are solid.
- `Set.offDiag` — delay or omit entirely; rarely needed.

### Hide (make available but don't put in the learner's inventory)
- `Set.eq_empty_iff_forall_not_mem` — use via hints rather than inventory; it's a rewrite lemma, not a concept.
- `Set.nonempty_iff_ne_empty` — similarly, use via hints.
- `Quotient.mk` vs `Quotient.mk'` — pick one and hide the other to avoid confusion.
- `Set.range_eq_univ` — a characterization lemma, not an inventory item.

### Gate (disable powerful tactics that bypass learning)

**Baseline disabled tactics** (always disabled unless explicitly re-enabled): `trivial`, `decide`, `native_decide`, `simp`, `aesop`, `simp_all`. These are assumed disabled at every level; world authors must not omit them.

**Course-specific tactic gating:**
- `tauto` — disable when teaching propositional reasoning about sets.
- `norm_num` — disable when the point is a proof-move, not computation.
- `linarith` — disable when arithmetic reasoning should be explicit.
- `omega` — disable at levels with arithmetic goals in concrete set examples (e.g., `{n : ℕ | n < 5}`, modular arithmetic, pairing functions); `omega` closes many natural-number goals that are supposed to be set-theoretic exercises.
- `ext` — initially hide to teach double-containment explicitly; introduce `ext` as a shortcut later.
- `exact?` / `apply?` — disable when the learner should be finding the move themselves.

**Lattice aliases for Set operations — CRITICAL exploit vector:**

`Set α` is a `CompleteBooleanAlgebra`. Every set-operation identity has a lattice-level alias that `simp` or direct `exact` can find, bypassing the intended proof moves entirely. These must be disabled via `DisabledTheorem` at any level where the learner is supposed to derive set identities by unfolding to logic.

| Set operation | Lattice alias family | Key lemmas to disable |
|--------------|---------------------|----------------------|
| `∪` = `⊔` (sup) | `sup_comm`, `sup_assoc`, `le_sup_left`, `le_sup_right`, `sup_le`, `sup_eq_left`, `sup_eq_right` |
| `∩` = `⊓` (inf) | `inf_comm`, `inf_assoc`, `inf_le_left`, `inf_le_right`, `le_inf`, `inf_eq_left`, `inf_eq_right` |
| `⊆` = `≤` | All partial-order lemmas: `le_antisymm`, `le_trans`, `le_refl` |
| `⋃` = `⨆` (iSup) | `iSup_le`, `le_iSup`, `iSup_le_iff` and their indexed variants |
| `⋂` = `⨅` (iInf) | `iInf_le`, `le_iInf`, `le_iInf_iff` and their indexed variants |
| `ᶜ` = `compl` | `compl_compl`, `compl_sup`, `compl_inf`, `compl_le_compl_iff_le` |
| `\` = `sdiff` | `sdiff_le`, `sdiff_sup`, `sdiff_inf_self_left` |
| distributive | `sup_inf_left`, `sup_inf_right`, `inf_sup_left`, `inf_sup_right` |

Additionally, many `Set.*` lemmas are themselves one-line closers:
- `Set.union_comm`, `Set.inter_comm` — close commutativity goals directly
- `Set.inter_subset_left`, `Set.inter_subset_right` — close subset goals directly
- `Set.subset_union_left`, `Set.subset_union_right` — close subset goals directly
- `Set.union_inter_distrib_left`, `Set.union_inter_distrib_right` — close distributivity goals

**Composition and structural lemmas to disable at teaching levels:**
- `Function.Injective.comp` — closes `Injective g → Injective f → Injective (g ∘ f)` directly
- `Function.Surjective.comp` — same for surjectivity
- `Function.Bijective.comp` — same for bijectivity
- `Function.LeftInverse.comp` / `Function.RightInverse.comp` — same pattern for inverses
- `Quotient.eq` — directly characterizes `⟦a⟧ = ⟦b⟧ ↔ a ≈ b`, trivializing proofs that should use `Quotient.sound`/`Quotient.exact` manually
- `Set.ext_iff` — trivializes set equality when the point is using `ext` tactic + manual double-containment

**Specific simp lemmas to watch as `DisabledTheorem` candidates** (even when `simp` is re-enabled, these trivialize core proof moves):
- `Set.mem_setOf_eq` — trivializes membership unfolding
- `Set.subset_def` — trivializes subset proofs
- `Set.image_subset_iff` — trivializes image containment
- `Set.mem_image` — trivializes image membership

---

## 7. Confidence Notes

### High confidence
- The set-operations and logic connection is extremely well supported in mathlib. There is no risk of missing API.
- `Function.Injective` / `Surjective` / `Bijective` and their composition laws are thoroughly covered.
- `Equiv` is well-structured with clear constructors.
- The partition ↔ equivalence correspondence exists (`Setoid.Partition.orderIso`) and is usable.
- `Countable` / `Encodable` / `Denumerable` hierarchy is clean in mathlib.
- Image/preimage API is extensive with good simp lemmas.

### Needs architect judgment
- **On-set function properties** (`MapsTo`, `InjOn`, etc.): These are mathematically important but the proof shapes are very similar to the global versions. The architect needs to decide how many levels to spend on these vs. using them as retrieval practice for the global-function cluster. My recommendation: dedicate a world to them, but keep it focused on the *differences* from global properties (e.g., `InjOn` can hold even when `Injective` fails).
- **Cantor's theorem placement**: It could be a boss of the functions world (it's purely about injective/surjective) or a boss of the countability world (it's the foundation of uncountability). I lean toward the countability world, but the architect should decide based on what makes the best capstone.
- **ℤ-from-ℕ×ℕ quotient construction**: This is a major motivating example but also a substantial integration exercise. It could be a boss of the quotient world or a standalone pset. The architect should decide based on whether the quotient world has room.
- **Indexed unions/intersections** (`iUnion`, `iInter`): These are new notation AND new proof moves (existential/universal over an index). They could be in the same world as binary operations or in a separate world. I lean toward separate — the binder notation is a genuine new burden.
- **How deep to go on `Encodable` internals**: The encode/decode pair is somewhat low-level. The course could focus on `Countable` (the mathematical concept) and treat `Encodable` as a supporting implementation detail, or it could treat the constructive interface as a first-class teaching target. The catalog description says "encodable types" explicitly, so I've included it as core, but the architect may want to demote it to supporting if the learner audience doesn't need constructive computation.
- **Subtype vs Set balance**: The course must teach both and connect them, but the ratio of levels is an architect decision. My estimate: subtypes deserve a full world because the coercion issues are a genuine obstacle.
