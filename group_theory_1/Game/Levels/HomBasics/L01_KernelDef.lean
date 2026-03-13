import Game.Metadata

World "HomBasics"
Level 1

Title "The Kernel of a Homomorphism"

Introduction
"
In the last world you showed that if `f(a) = f(b)`, then `f(a · b⁻¹) = 1`.
The set of elements that `f` sends to `1` has a name: the **kernel**.

`f.ker = {x ∈ G | f(x) = 1}`

In Lean, `f.ker` is a `Subgroup G` (it's always a subgroup — closed under
multiplication, contains `1`, closed under inverses).

The key unfolding lemma is `MonoidHom.mem_ker`:

`MonoidHom.mem_ker : x ∈ f.ker ↔ f x = 1`

Use `rw [MonoidHom.mem_ker]` to convert between kernel membership and
the equation `f x = 1`.

Prove that `1` is always in the kernel.
"

/-- The kernel of a group homomorphism `f : G →* H`.

`f.ker` is the subgroup `{x ∈ G | f x = 1}`.

Elements in the kernel are \"invisible\" to `f` — they all get
mapped to the identity. -/
DefinitionDoc MonoidHom.ker as "MonoidHom.ker"

NewDefinition MonoidHom.ker

/-- `MonoidHom.mem_ker` says: for a group homomorphism `f : G →* H`,

`x ∈ f.ker ↔ f x = 1`

Use `rw [MonoidHom.mem_ker]` to unfold kernel membership into
the equation `f x = 1`, or use it at a hypothesis with
`rw [MonoidHom.mem_ker] at h`. -/
TheoremDoc MonoidHom.mem_ker as "MonoidHom.mem_ker" in "Hom"

NewTheorem MonoidHom.mem_ker

TheoremTab "Hom"

DisabledTactic simp group
DisabledTheorem OneMemClass.one_mem

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) :
    (1 : G) ∈ f.ker := by
  Hint "The goal is `1 ∈ f.ker`. Use `rw [MonoidHom.mem_ker]` to
  unfold this to `f 1 = 1`."
  rw [MonoidHom.mem_ker]
  Hint (hidden := true) "The goal is `f 1 = 1`. You proved this in
  the last world — use `exact map_one f`."
  exact map_one f

Conclusion
"
The kernel of any homomorphism always contains `1` — since
`f(1) = 1` by `map_one`, the identity is always \"invisible\" to `f`.

The real question is: **how big is the kernel?**

- If `ker(f) = {1}` (just the identity), then `f` loses no
  information — distinct inputs produce distinct outputs.
  This means `f` is *injective*.
- If `ker(f) = G` (everything maps to `1`), then `f` is the
  trivial homomorphism — it loses all information.

The kernel measures how much information `f` destroys. You'll
formalize the connection between trivial kernel and injectivity
by the end of this world.

The pattern `rw [MonoidHom.mem_ker]` → algebra is the
**kernel-reasoning move**. You'll use it constantly.
"
