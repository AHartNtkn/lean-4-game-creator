# Coverage Review: functions_relations

**Reviewed**: 2026-03-23
**Coverage map**: `functions_relations/coverage-map.md`
**Course description**: `long_term.md` item #2

---

## 1. Scope Gaps

### P1: Schroeder-Bernstein theorem missing

The Cantor-Schroeder-Bernstein theorem (`Function.Embedding.schroeder_bernstein` in `Mathlib.SetTheory.Cardinal.SchroederBernstein`) states: given injections `α ↪ β` and `β ↪ α`, there exists an equivalence `α ≃ β`. This is THE theorem connecting injections to equivalences. The coverage map already covers `Function.Embedding`, `Equiv`, `Equiv.ofBijective`, and the composition/extraction laws for injectivity — but never bridges from "mutual injections" to "equivalence."

The course description says this is "where you teach the difference between equality, equivalence, and isomorphism." Schroeder-Bernstein is directly about when injections suffice for equivalence. It belongs in the MATH axis (core or at least supporting), with a concrete example (e.g., `ℕ ↪ ℤ` and `ℤ ↪ ℕ` yield `ℕ ≃ ℤ`), and its proof shape (fixed-point / partition argument) belongs in the MOVE axis.

Mitigation: the proof in mathlib is nonconstructive and moderately complex, so it may not be suitable as a level the player proves from scratch. But it should appear as a `NewTheorem` the player uses, and its *statement* should be a teaching moment. A level where the player *applies* Schroeder-Bernstein to derive an equivalence from two injections would be pedagogically valuable.

**Severity: P1** — important theorem in the course's topic area, but the course is still coherent without it. Not P0 because the course description does not explicitly name it.

### P2: `contrapose` / `contrapositive` tactic not mentioned

The `contrapose` tactic is a common proof move in injectivity proofs (contrapositive of `f a = f b → a = b` is `a ≠ b → f a ≠ f b`). It's absent from both the MOVE axis and LEAN axis. It's also useful for proving `s ⊆ t` by contrapositive. This is a minor gap since `by_contra` + `push_neg` can achieve the same effect, but `contrapose` is cleaner and commonly used in mathlib-style proofs.

**Severity: P2** — nice to have, not blocking.

### No P0 scope gaps found

Every topic, definition, and theorem family mentioned in `long_term.md` item #2 appears in the coverage map:
- Sets as predicates (`Set α = α → Prop`)
- Images/preimages (`Set.image`, `Set.preimage`)
- Restriction to subsets (`Set.restrict`, on-set variants)
- Injective/surjective/bijective-on-a-set maps (`MapsTo`, `InjOn`, `SurjOn`, `BijOn`)
- Relations as sets of pairs (both `Set (α × α)` and `α → α → Prop`)
- Bundled equivalences (`Equiv`)
- Partial equivalences (`PartialEquiv`)
- Subtypes (`Subtype`, `↥s`)
- Countable sets (`Set.Countable`)
- Encodable types (`Encodable`, `Denumerable`)
- Equality vs equivalence vs isomorphism (`=`, `≈`, `≃`) — explicitly covered in TRANSFER axis item 207

---

## 2. Mathlib Discrepancies

### All API names verified correct

Every API name I checked against current mathlib4 documentation matches:

| Coverage map name | Status | Module |
|---|---|---|
| `Function.cantor_surjective` | Correct | `Mathlib.Logic.Function.Basic` |
| `Function.cantor_injective` | Correct | `Mathlib.Logic.Function.Basic` |
| `Setoid.ker` / `Setoid.kerLift` | Correct | `Mathlib.Data.Setoid.Basic` |
| `Setoid.quotientKerEquivRange` | Correct | `Mathlib.Data.Setoid.Basic` |
| `Setoid.quotientKerEquivOfSurjective` | Correct | `Mathlib.Data.Setoid.Basic` |
| `Setoid.quotientEquivClasses` | Correct | `Mathlib.Data.Setoid.Partition` |
| `Setoid.IsPartition` | Correct | `Mathlib.Data.Setoid.Partition` |
| `Setoid.Partition.orderIso` | Correct | `Mathlib.Data.Setoid.Partition` |
| `Equiv.ofBijective` | Correct | `Mathlib.Logic.Equiv.Defs` |
| `Equiv.ofInjective` | Correct | `Mathlib.Logic.Equiv.Basic` |
| `Equiv.Set.univ` / `.union` / `.sumCompl` | Correct | `Mathlib.Logic.Equiv.Set` |
| `Denumerable.eqv` | Correct | `Mathlib.Logic.Denumerable` |
| `Encodable.encode` / `.decode` | Correct | `Mathlib.Logic.Encodable.Basic` |
| `Set.MapsTo` / `InjOn` / `SurjOn` / `BijOn` | Correct | `Mathlib.Data.Set.Function` |
| `IndexedPartition` | Correct | `Mathlib.Data.Setoid.Partition` |

### No missing mathlib content found

The coverage map covers the relevant mathlib modules thoroughly. The only significant mathlib theorem in this area that's absent is Schroeder-Bernstein (flagged above as P1 scope gap).

---

## 3. Proof-Move Gaps

### P2: Missing `contrapose` move

As noted in scope gaps. The `contrapose` tactic turns `A → B` into `¬B → ¬A`. Common in:
- Injectivity: contrapositive of `f a = f b → a = b` is `a ≠ b → f a ≠ f b`
- Subset: contrapositive of `x ∈ s → x ∈ t` is `x ∉ t → x ∉ s`
- Countability: "if X were countable, then... contradiction"

This is not blocking because `by_contra` + `push_neg` achieves the same results.

### Clusters are otherwise realistic and complete

The 10 main clusters (plus sub-clusters 7b, 7c, 7d) accurately reflect how proofs in this area work:
- Cluster 1 (set membership/logic) correctly identifies the `∪↔∨`, `∩↔∧`, `ᶜ↔¬` correspondence
- Cluster 3 (image/preimage) correctly captures the existential-witness shape for images
- Cluster 4 (injectivity/surjectivity) includes both composition and extraction, which is the right split
- Cluster 7 (quotient) correctly sequences: `mk` → `sound`/`exact` → `lift` → `inductionOn` → `map` → `out`
- Cluster 7d (kernel→quotient→range) correctly identifies this as a bridge between quotient and function worlds
- Cluster 7b (indexed unions) correctly distinguishes the `∃`/`∀` proof shape from binary `∨`/`∧`

No unrealistic clusters found. The sequencing within clusters is sound.

---

## 4. Example Gaps

### P2: No example for Schroeder-Bernstein

If Schroeder-Bernstein is added (P1 above), it needs a concrete example. Natural candidates:
- `ℕ ↪ ℤ` (via `Nat.cast`) and `ℤ ↪ ℕ` (via some injection) yield `ℕ ≃ ℤ`
- `{n : ℕ | Even n} ↪ ℕ` and `ℕ ↪ {n : ℕ | Even n}` (via doubling) yield equivalence

### P2: No counterexample for "injective + surjective components don't imply bijective composite"

The map has a counterexample for "injective composition → components injective" (line 308) but does not have the dual: `g` surjective and `f` surjective doesn't automatically give `g ∘ f` bijective (well, it gives surjectivity but not injectivity). This is minor since composition of surjections giving surjectivity IS taught.

### Otherwise thorough

The example plan is comprehensive. Every major definition has at least one concrete example. Key counterexamples are planned:
- Injective not surjective (doubling)
- Surjective not injective (halving)
- Non-equivalence relations (three types: not-symmetric, not-transitive, not-reflexive)
- Non-partitions (overlapping, empty part)
- Image/preimage asymmetry (both directions)
- The ℤ-from-ℕ×ℕ construction is an excellent integration example

---

## 5. Exploit Gaps

### P2: `Equiv.ofBijective` as an exploit for Equiv-building levels

If a level intends for the player to build an `Equiv` from `toFun`/`invFun`/`left_inv`/`right_inv` (Cluster 9), then `Equiv.ofBijective` is a one-call shortcut: prove `Bijective f` and call `Equiv.ofBijective`. The coverage map lists this as a `NewTheorem` (line 79) but does not flag it as a `DisabledTheorem` candidate at levels where the point is manual `Equiv` construction. The architect should decide per-level whether this is a teaching tool or an exploit.

### P2: `Quotient.eq` vs `Quotient.sound`/`Quotient.exact`

The coverage map correctly identifies `Quotient.eq` (line 536) as a `DisabledTheorem` candidate since it directly gives `⟦a⟧ = ⟦b⟧ ↔ a ≈ b`, trivializing proofs that should use `sound`/`exact` manually. This is good.

### P2: `Set.Finite.countable` as a countability exploit

If any level involves proving a finite set is countable, `Set.Finite.countable` closes it in one call. Not mentioned in the exploit section. Minor because the course likely won't have levels where this specific shortcut matters.

### Exploit awareness is otherwise excellent

The lattice-alias section (lines 510-530) is thorough and correctly identifies the `CompleteBooleanAlgebra` instance on `Set α` as the root cause. The specific `Set.*` one-liner lemmas (lines 526-529) are correctly flagged. The composition lemmas (`Function.Injective.comp` etc.) are correctly identified. The `omega` gating for arithmetic goals is noted.

---

## 6. Overall Verdict

**PASS**

This is a thorough, well-structured coverage map. The scope aligns with the course description in `long_term.md`. All mathlib API names are correct. The proof-move clusters are realistic and well-sequenced. The example plan provides concrete instances for every major concept. The exploit awareness is detailed and identifies the key vectors (lattice aliases, composition lemmas, set-operation lemmas, `omega`).

The P1 gap (Schroeder-Bernstein) is a real omission in the topic space but does not make the course incoherent — it can be added during world authoring as a bonus level or `NewTheorem`. The P2 gaps are all minor and addressable during authoring without changing the coverage structure.

### Summary of findings

| Category | P0 | P1 | P2 |
|---|---|---|---|
| Scope gaps | 0 | 1 (Schroeder-Bernstein) | 1 (`contrapose`) |
| Mathlib discrepancies | 0 | 0 | 0 |
| Proof-move gaps | 0 | 0 | 1 (`contrapose`) |
| Example gaps | 0 | 0 | 2 |
| Exploit gaps | 0 | 0 | 3 |
| **Total** | **0** | **1** | **7** |
