import GameServer.Commands
import Mathlib.Data.Set.Basic

/-!
# Course Metadata

Shared documentation entries for tactics and definitions that are used
across multiple worlds (particularly for disabled items that need docs).
Import this file from any level file that uses DisabledTactic.
-/

/-- `tauto` is an automation tactic that closes goals provable by
propositional logic alone. It is disabled in this course to ensure
you learn the underlying proof steps. -/
TacticDoc tauto

/-- `norm_num` is an automation tactic that closes numeric goals
like `2 + 3 = 5` or `7 > 3`. It is disabled in this course to
ensure you engage with the proof structure rather than relying on
automation. -/
TacticDoc norm_num

/-- `trivial` is an automation tactic that closes simple goals.
It is disabled in this course. -/
TacticDoc trivial

/-- `decide` is an automation tactic that closes decidable propositions
by computation. It is disabled in this course. -/
TacticDoc decide

/-- `native_decide` is like `decide` but uses native code evaluation.
It is disabled in this course. -/
TacticDoc native_decide

/-- `simp` is a powerful simplification tactic that applies a database of
rewriting rules. It is disabled in early worlds of this course to ensure
you learn the individual proof steps. -/
TacticDoc simp

/-- `aesop` is a general-purpose automation tactic. It is disabled in this
course to ensure you learn the underlying proof techniques. -/
TacticDoc aesop

/-- `simp_all` is a variant of `simp` that also simplifies hypotheses.
It is disabled in this course. -/
TacticDoc simp_all

/-! ## Disabled theorem documentation

These theorems are disabled in specific levels to prevent one-shot
solutions that bypass the intended lesson. -/

/-- `subset_refl` states that `A ⊆ A` for any set `A`. Disabled in early
levels where you are learning the subset proof pattern. -/
TheoremDoc subset_refl as "subset_refl" in "Set"

/-- `Set.Subset.refl` states that `A ⊆ A` for any set `A`. Disabled in early
levels where you are learning the subset proof pattern. -/
TheoremDoc Set.Subset.refl as "Set.Subset.refl" in "Set"

/-- `le_refl` states that `a ≤ a`. For sets, `⊆` is `≤` in the lattice
order, so `le_refl` also proves `A ⊆ A`. Disabled in early levels. -/
TheoremDoc le_refl as "le_refl" in "Order"

/-- `Set.Subset.trans` states that if `A ⊆ B` and `B ⊆ C` then `A ⊆ C`.
Disabled in levels where you are learning to chain subset hypotheses. -/
TheoremDoc Set.Subset.trans as "Set.Subset.trans" in "Set"

/-- `le_trans` states that if `a ≤ b` and `b ≤ c` then `a ≤ c`. For sets,
this gives subset transitivity. Disabled in levels teaching chaining. -/
TheoremDoc le_trans as "le_trans" in "Order"

/-- `Set.empty_subset` states that `∅ ⊆ A` for any set `A`. Disabled in
levels where you are learning about the empty set and vacuous truth. -/
TheoremDoc Set.empty_subset as "Set.empty_subset" in "Set"

/-- `bot_le` states that `⊥ ≤ a`. For sets, `⊥ = ∅`, so this gives
`∅ ⊆ A`. Disabled in levels teaching the empty set. -/
TheoremDoc bot_le as "bot_le" in "Order"

/-- `Set.subset_univ` states that `A ⊆ Set.univ` for any set `A`. Disabled
in levels where you are learning about the universal set. -/
TheoremDoc Set.subset_univ as "Set.subset_univ" in "Set"

/-- `le_top` states that `a ≤ ⊤`. For sets, `⊤ = Set.univ`, so this gives
`A ⊆ Set.univ`. Disabled in levels teaching the universal set. -/
TheoremDoc le_top as "le_top" in "Order"

/-- `and_comm` states that `P ∧ Q ↔ Q ∧ P`. Disabled in levels where
conjunction manipulation is the intended lesson. -/
TheoremDoc and_comm as "and_comm" in "Logic"

/-- `And.comm` states that `P ∧ Q ↔ Q ∧ P`. Disabled in levels where
conjunction manipulation is the intended lesson. -/
TheoremDoc And.comm as "And.comm" in "Logic"

/-- `le_antisymm` states that if `a ≤ b` and `b ≤ a` then `a = b`. For sets,
this gives `Set.Subset.antisymm`. Disabled in boss levels. -/
TheoremDoc le_antisymm as "le_antisymm" in "Order"

/-- `Subset.antisymm` states that if `A ⊆ B` and `B ⊆ A` then `A = B`.
Disabled in boss levels where you must prove this from `ext`. -/
TheoremDoc Subset.antisymm as "Subset.antisymm" in "Set"

/-- `Set.eq_of_subset_of_subset` states that if `A ⊆ B` and `B ⊆ A` then `A = B`.
Disabled in boss levels. -/
TheoremDoc Set.eq_of_subset_of_subset as "Set.eq_of_subset_of_subset" in "Set"

/-- `LE.le.antisymm` states that if `a ≤ b` and `b ≤ a` then `a = b`.
For sets, this is subset antisymmetry. Disabled in boss levels. -/
TheoremDoc LE.le.antisymm as "LE.le.antisymm" in "Order"

/-- `eq_of_subset_of_subset` states that if `A ⊆ B` and `B ⊆ A` then `A = B`.
Disabled in boss levels. -/
TheoremDoc eq_of_subset_of_subset as "eq_of_subset_of_subset" in "Set"
