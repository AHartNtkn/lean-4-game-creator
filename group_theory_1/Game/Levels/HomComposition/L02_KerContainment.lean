import Game.Metadata

World "HomComposition"
Level 2

Title "Kernel Containment"

Introduction
"
If `f(x) = 1`, what happens when we apply `g` afterward?

`(g ∘ f)(x) = g(f(x)) = g(1) = 1`

So anything in `ker(f)` is automatically in `ker(g ∘ f)`: the composition's
kernel is at least as large as `f`'s kernel.

The proof combines kernel reasoning (unfold `mem_ker`) with the
composition unfolding (`comp_apply`) and the hom-property (`map_one`).
"

TheoremTab "Hom"

DisabledTactic simp group

Statement (G H K : Type*) [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (x : G) (hx : x ∈ f.ker) :
    x ∈ (g.comp f).ker := by
  Hint "Unfold kernel membership in both the hypothesis and the goal:
  `rw [MonoidHom.mem_ker] at {hx} ⊢`."
  rw [MonoidHom.mem_ker] at hx ⊢
  Hint "The goal is `(g.comp f) x = 1`. Unfold the composition:
  `rw [MonoidHom.comp_apply]`."
  rw [MonoidHom.comp_apply]
  Hint "The goal is `g (f x) = 1`. Substitute `{hx} : f x = 1`:
  `rw [{hx}]`."
  rw [hx]
  Hint (hidden := true) "The goal is `g 1 = 1`. Use `exact map_one g`."
  exact map_one g

Conclusion
"
The chain:
```
(g ∘ f)(x) = g(f(x))   — comp_apply
           = g(1)       — f(x) = 1 (kernel hypothesis)
           = 1          — map_one
```

This proves `ker(f) ≤ ker(g ∘ f)`: every element killed by `f`
is also killed by the composition.

Algebraically, this is obvious: if `f` already maps `x` to `1`,
then applying `g` afterward sends `1` to `1`. The composition
\"inherits\" all of `f`'s kernel, and potentially more — elements
where `f(x) ≠ 1` but `g(f(x)) = 1` are also in `ker(g ∘ f)`.

In the next level you'll see the dual: `range(g ∘ f) ≤ range(g)`.
Together they say: **composition is lossy — kernels grow, ranges shrink**.

On paper: *If `x ∈ ker(f)`, then `f(x) = 1`, so
`(g ∘ f)(x) = g(1) = 1`, hence `x ∈ ker(g ∘ f)`.*
"
