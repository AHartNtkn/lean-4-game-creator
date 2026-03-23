import Game.Metadata

set_option allowUnsafeReducibility true in
attribute [irreducible] Matrix.of Matrix.transpose Matrix.diagonal Matrix.diag

/-! ## TheoremDocs for commonly disabled theorems

These are placed here so every level file can reference them when
using `DisabledTheorem`. The GameServer requires `TheoremDoc` to
appear before (or in an imported file above) `DisabledTheorem`. -/

/-- `Matrix.transpose_transpose` proves `Mᵀᵀ = M` directly.
Disabled so you prove it yourself using `ext` and `transpose_apply`. -/
TheoremDoc Matrix.transpose_transpose as "Matrix.transpose_transpose" in "Matrix"

/-- `Matrix.transpose_add` proves `(M + N)ᵀ = Mᵀ + Nᵀ` directly.
Disabled so you prove it using `ext`, `transpose_apply`, and `add_apply`. -/
TheoremDoc Matrix.transpose_add as "Matrix.transpose_add" in "Matrix"

/-- `Matrix.diagonal_apply` gives the if-then-else form:
`(diagonal d) i j = if i = j then d i else 0`.
Disabled so you use the more explicit `diagonal_apply_eq` and
`diagonal_apply_ne` lemmas instead. -/
TheoremDoc Matrix.diagonal_apply as "Matrix.diagonal_apply" in "Matrix"

/-- `Matrix.diag_diagonal` proves `diag (diagonal d) = d` directly.
Disabled so you prove it yourself using `ext`, `diag_apply`, and
`diagonal_apply_eq`. -/
TheoremDoc Matrix.diag_diagonal as "Matrix.diag_diagonal" in "Matrix"

/-- `Matrix.diagonal_transpose` proves `(diagonal d)ᵀ = diagonal d`
directly. Disabled so you prove entry-level facts about transposed
diagonal matrices yourself. -/
TheoremDoc Matrix.diagonal_transpose as "Matrix.diagonal_transpose" in "Matrix"

/-- `Matrix.diagonal_add` proves `diagonal d + diagonal e = diagonal (d + e)`
directly. Disabled so you prove it using ext, case split, and diagonal lemmas. -/
TheoremDoc Matrix.diagonal_add as "Matrix.diagonal_add" in "Matrix"

/-- `Matrix.diag_transpose` relates `diag (Mᵀ)` to `diag M`.
Disabled so you work with transpose and diagonal individually. -/
TheoremDoc Matrix.diag_transpose as "Matrix.diag_transpose" in "Matrix"
