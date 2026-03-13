import Game.Metadata

World "HomBasics"
Level 8

Title "Boss — Injective iff Trivial Kernel"

Introduction
"
The central theorem of this world: a group homomorphism is injective
if and only if its kernel is trivial.

`f.ker = ⊥ ↔ Function.Injective f`

You need to prove both directions:

**Forward** (`ker = ⊥ → injective`): If `f(a) = f(b)`, show `a = b`.
The chain: `f(ab⁻¹) = f(a)f(b)⁻¹ = 1`, so `ab⁻¹ ∈ ker = ⊥`, so
`ab⁻¹ = 1`, so `a = b`. (This is Level 7.)

**Backward** (`injective → ker = ⊥`): Show `f.ker = ⊥` by `ext`:
prove `x ∈ f.ker ↔ x ∈ ⊥`, i.e., `f x = 1 ↔ x = 1`. The forward
implication uses injectivity (Level 6). The backward is `map_one`.

Start with `refine ⟨?_, ?_⟩` to split the `↔`.
"

TheoremTab "Hom"

/-- Disabled — you are proving this yourself right now. -/
TheoremDoc MonoidHom.ker_eq_bot_iff as "MonoidHom.ker_eq_bot_iff" in "Hom"

DisabledTactic simp group
DisabledTheorem MonoidHom.ker_eq_bot_iff injective_iff_map_eq_one injective_iff_map_eq_one'

Statement (G H : Type*) [Group G] [Group H] (f : G →* H) :
    f.ker = ⊥ ↔ Function.Injective f := by
  Hint "Split the `↔` with `refine ⟨?_, ?_⟩`."
  refine ⟨?_, ?_⟩
  · -- Forward: ker = ⊥ → injective
    Hint "Introduce the hypothesis and unfold `Function.Injective`:
    `intro hk a b hab`."
    intro hk a b hab
    Hint "The goal is `a = b`. Transform it using `← mul_inv_eq_one`,
    then `← Subgroup.mem_bot`, then `← {hk}`, then `MonoidHom.mem_ker`."
    rw [← mul_inv_eq_one]
    rw [← Subgroup.mem_bot]
    rw [← hk]
    rw [MonoidHom.mem_ker]
    Hint "Push `f` through: `rw [map_mul]`, then `rw [map_inv]`,
    then `rw [{hab}]`."
    rw [map_mul, map_inv, hab]
    Hint (hidden := true) "Use `exact mul_inv_cancel (f b)`."
    exact mul_inv_cancel (f b)
  · -- Backward: injective → ker = ⊥
    Hint "Introduce the injectivity hypothesis: `intro hf`.
    Then prove `f.ker = ⊥` pointwise — remember `ext` from
    SubgroupBasics? To show two subgroups are equal, show they
    have the same elements: `ext x`."
    intro hf
    ext x
    Hint "The goal is `x ∈ f.ker ↔ x ∈ ⊥`. Unfold both sides:
    `rw [MonoidHom.mem_ker, Subgroup.mem_bot]`."
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    Hint "Split the `↔`: `refine ⟨?_, ?_⟩`."
    refine ⟨?_, ?_⟩
    · -- f x = 1 → x = 1
      Hint "Introduce `hx : f x = 1`. Rewrite `1` as `f 1`:
      `rw [← map_one f] at hx`. Then `exact hf hx`."
      intro hx
      rw [← map_one f] at hx
      exact hf hx
    · -- x = 1 → f x = 1
      Hint (hidden := true) "Introduce `hx : x = 1`, then
      `rw [hx]` and `exact map_one f`."
      intro hx
      rw [hx]
      exact map_one f

Conclusion
"
Congratulations on completing **Kernel and Image**!

You proved the fundamental connection:

> **A group homomorphism is injective if and only if its kernel is trivial.**

Both directions:
- **ker = ⊥ → injective**: If `f(a) = f(b)`, then
  `f(ab⁻¹) = 1`, so `ab⁻¹ ∈ ker = {1}`, so `a = b`.
- **injective → ker = ⊥**: If `f(x) = 1 = f(1)` and `f` is
  injective, then `x = 1`.

This theorem says: **the kernel measures exactly the failure of
injectivity**. The bigger the kernel, the more information `f` loses.

Your tools from this world:

| Item | Type | Purpose |
|------|------|---------|
| `f.ker` | Definition | Kernel subgroup: `{x | f x = 1}` |
| `MonoidHom.mem_ker` | Theorem | `x ∈ f.ker ↔ f x = 1` |
| `f.range` | Definition | Range subgroup: `{y | ∃ x, f x = y}` |
| `MonoidHom.mem_range` | Theorem | `y ∈ f.range ↔ ∃ x, f x = y` |
| `Function.Injective` | Definition | `∀ a b, f a = f b → a = b` |
| `mul_inv_eq_one` | Theorem | `a * b⁻¹ = 1 ↔ a = b` |
| `specialize` | Tactic | Pin a universal hypothesis to a specific value |

Proof moves:
- **Kernel reasoning**: `rw [mem_ker]` → algebra → `f x = 1`
- **Image reasoning**: `obtain` witness → transform → `⟨w, proof⟩`

The **kernel navigation diamond** summarizes the key equivalences:

```
        x ∈ f.ker
       ↗         ↘
   f x = 1    x ∈ ⊥
       ↘         ↗
         x = 1
```

Each arrow is one `rw` step. The forward direction of the boss
chains the left side down; the backward direction chains the
right side down.

On paper: *\"A homomorphism `f` is injective iff `ker(f)` is trivial.
The kernel is the obstruction to injectivity: elements that collapse
together under `f` differ by a kernel element.\"*

**Important**: this equivalence depends on `f` being a *homomorphism*.
For an arbitrary function, having only one preimage of `0` (or `1`)
does not imply injectivity. The homomorphism property — `f(ab) = f(a)f(b)` —
is what connects the kernel to global injectivity.

Dually, just as `ker(f) = ⊥` means `f` is injective,
`range(f) = ⊤` means `f` is surjective. The kernel measures
information *destroyed*; the range measures information *reached*.

Looking further ahead: the first isomorphism theorem will make this
precise — `G / ker(f) ≅ range(f)`, so the kernel is exactly the
\"redundancy\" that must be collapsed to recover the image.

What's next: you'll practice these skills under varied settings in
the problem set, then meet *normal* subgroups — a property that
every kernel automatically has.
"
