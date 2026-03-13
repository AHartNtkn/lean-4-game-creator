import Game.Metadata

World "NormalDef"
Level 9

Title "Boss — Kernel is Normal"

Introduction
"
Prove the central theorem of this world: the kernel of any group
homomorphism is a normal subgroup.

You need to build a value of type `f.ker.Normal` — a structure with one
field proving the conjugation property. You've practiced every piece:

- **Level 2**: Normal constructor: `refine ⟨?_⟩` + `intro n hn g`
- **Level 6**: Kernel conjugation algebra: unfold `mem_ker`, push `f`
  through, substitute, cancel

Combine them.
"

/-- Disabled — you are proving this yourself. -/
TheoremDoc MonoidHom.normal_ker as "MonoidHom.normal_ker" in "Normal"

/-- Disabled — proves `g⁻¹ * n * g ∈ N` directly. -/
TheoremDoc Subgroup.Normal.conj_mem' as "conj_mem'" in "Normal"

/-- Disabled — characteristic subgroups are automatically normal. -/
TheoremDoc Subgroup.normal_of_characteristic as "normal_of_characteristic" in "Normal"

TheoremTab "Normal"

DisabledTactic simp group
DisabledTheorem MonoidHom.normal_ker Subgroup.Normal.conj_mem Subgroup.Normal.conj_mem' Subgroup.normal_of_characteristic

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) :
    f.ker.Normal := by
  Hint "Build the Normal structure. Use `refine ⟨?_⟩` to open it."
  Branch
    constructor
    intro n hn g
    rw [MonoidHom.mem_ker] at hn ⊢
    rw [map_mul, map_mul, map_inv, hn, mul_one, mul_inv_cancel]
  refine ⟨?_⟩
  Hint "Introduce the universally quantified variables: `intro n hn g`.
  You need to prove `g * n * g⁻¹ ∈ f.ker`."
  intro n hn g
  Hint "Unfold kernel membership. You can unfold both the hypothesis
  and the goal at once: `rw [MonoidHom.mem_ker] at hn ⊢`."
  Branch
    rw [MonoidHom.mem_ker] at hn
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_inv, hn, mul_one, mul_inv_cancel]
  rw [MonoidHom.mem_ker] at hn ⊢
  Hint "Push `f` through `g * n * g⁻¹`:
  `rw [map_mul, map_mul, map_inv]`."
  rw [map_mul, map_mul, map_inv]
  Hint "Substitute `{hn} : f n = 1` and cancel: `rw [{hn}, mul_one, mul_inv_cancel]`."
  rw [hn, mul_one, mul_inv_cancel]

Conclusion
"
Every kernel is a normal subgroup. This is the foundational link
between homomorphisms and quotient groups.

On paper: *Let `f : G → H` be a homomorphism and `n ∈ ker(f)`. For
any `g ∈ G`:*

*`f(gng⁻¹) = f(g) · f(n) · f(g)⁻¹ = f(g) · 1 · f(g)⁻¹ = 1`*

*so `gng⁻¹ ∈ ker(f)`. Hence `ker(f)` is normal in `G`.*

The **conjugation-check** move is the standard technique for proving
normality: given `n ∈ N` and `g ∈ G`, show `g * n * g⁻¹ ∈ N` by
algebraic manipulation. For kernels, \"algebraic manipulation\" means
pushing `f` through the expression and using `f(n) = 1`.

Proof moves learned:
- **Conjugation-check**: to prove `N.Normal`, show
  `g * n * g⁻¹ ∈ N` for all `n ∈ N`, `g ∈ G`
- **Normal constructor**: `refine ⟨?_⟩` + `intro n hn g`
- **Kernel normality argument**: unfold `mem_ker`, push `f` through,
  substitute `f(n) = 1`, cancel

Why does normality matter? Here's the concrete reason: to multiply
cosets `(aN)(bN) = (ab)N`, you need the result to be independent of
which representatives you pick. If `n₁ ∈ N`, then `(an₁)b = a(n₁b)
= a · b · (b⁻¹n₁b)`. For this to land in `(ab)N`, you need
`b⁻¹n₁b ∈ N` — which is exactly the normality condition. Without
normality, different representatives give different cosets, and
`G / N` is just a set of cosets, not a group.

**Warning**: The *converse* is false — not every normal subgroup is a
kernel... unless you construct the right homomorphism. In fact, `N` is
normal if and only if `N` is the kernel of the natural map `G → G/N`.
That's the quotient construction you'll see later.
"
