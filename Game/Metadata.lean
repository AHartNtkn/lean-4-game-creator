import GameServer
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Hom.Defs

/-- Build a subgroup with a specific carrier by proving three closure properties.
After `apply Subgroup.mk_carrier`, you get three goals: `mul_mem`, `one_mem`,
and `inv_mem` — each with the carrier already filled in. -/
theorem Subgroup.mk_carrier {G : Type*} [Group G] (S : Set G)
    (hmul : ∀ (a b : G), a ∈ S → b ∈ S → a * b ∈ S)
    (hone : (1 : G) ∈ S)
    (hinv : ∀ (x : G), x ∈ S → x⁻¹ ∈ S) :
    ∃ H : Subgroup G, H.carrier = S :=
  ⟨{
    carrier := S
    mul_mem' := fun {a} {b} => hmul a b
    one_mem' := hone
    inv_mem' := fun {x} => hinv x
  }, rfl⟩

/-- Build a group homomorphism by providing a function and proving it
preserves multiplication. After `apply MonoidHom.mk_fun (fun g => ...)`,
you get one goal: prove `∀ a b, f (a * b) = f a * f b`. -/
theorem MonoidHom.mk_fun {G H : Type*} [Group G] [Group H] (f : G → H)
    (hf : ∀ a b : G, f (a * b) = f a * f b) :
    ∃ φ : G →* H, ∀ g, φ g = f g :=
  ⟨MonoidHom.mk' f hf, fun _ => rfl⟩
