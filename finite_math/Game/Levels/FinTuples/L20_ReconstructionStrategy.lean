import Game.Metadata

World "FinTuples"
Level 20

Title "Reconstructing from Head and Tail"

Introduction "
# The Reconstruction Strategy

In Level 18, you proved a tuple equals `![...]` by checking
each index. There's a second strategy: **reconstruct**
the tuple from its head and tail using `Fin.cons_self_tail`.

Given information about the head (`f 0`) and tail (`Fin.tail f`)
of a tuple, you can determine the full tuple:

1. `have key := (Fin.cons_self_tail f).symm` — this gives
   `key : f = Fin.cons (f 0) (Fin.tail f)`
2. `rw [h0, ht] at key` — substitute known values to get
   `key : f = Fin.cons 10 ![20, 30]` (which is `![10, 20, 30]`)
3. `exact key` — close the goal

You practiced `.symm` in Level 19 — flipping equations to get the
direction you need. Here you'll combine `.symm` with `rw ... at`
to substitute known values into the reconstruction identity.

This is a different proof technique from the `ext` + case split
approach. Both work — the reconstruction approach is often shorter.

**Your task**: Reconstruct `f` from its head and tail.
"

/-- Reconstruct a tuple from its head and tail. -/
Statement (f : Fin 3 → ℕ) (h0 : f 0 = 10) (ht : Fin.tail f = ![20, 30]) :
    f = ![10, 20, 30] := by
  Hint "Start with `have key := (Fin.cons_self_tail f).symm`.
  This gives `key : f = Fin.cons (f 0) (Fin.tail f)`."
  have key := (Fin.cons_self_tail f).symm
  Hint "Now substitute the known head and tail into `key`:
  `rw [h0, ht] at key`.
  This transforms `key` into `f = Fin.cons 10 ![20, 30]`
  (which is `f = ![10, 20, 30]`)."
  rw [h0, ht] at key
  Hint "Now `key` matches the goal exactly. Use `exact key`."
  exact key

Conclusion "
The reconstruction strategy:

1. `have key := (Fin.cons_self_tail f).symm` — decompose
2. `rw [values] at key` — substitute known components
3. `exact key` — close the goal

This complements the `ext` + case split approach from Level 18:
- **ext + cases**: work index by index (good when you know individual values)
- **Reconstruction**: work structurally (good when you know head and tail)

The boss will ask you to combine both approaches in a single proof.
"

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
