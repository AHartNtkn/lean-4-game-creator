import Game.Metadata
import Mathlib.Data.Fin.Tuple.Basic

#check @Fin.cons_zero
#check @Fin.cons_succ  
#check @Fin.snoc_last
#check @Fin.snoc_castSucc
#check @Fin.tail
#check @Fin.tail_cons
#check @Fin.init_snoc

-- Test basic cons
example : Fin.cons (10 : ℕ) ![20, 30] 0 = 10 := by
  exact Fin.cons_zero 10 ![20, 30]

-- Test cons_succ
example (i : Fin 2) : Fin.cons (10 : ℕ) ![20, 30] i.succ = ![20, 30] i := by
  exact Fin.cons_succ 10 ![20, 30] i

-- Test snoc
example : Fin.snoc (![10, 20] : Fin 2 → ℕ) 30 (Fin.last 2) = 30 := by
  exact Fin.snoc_last 30 ![10, 20]

-- Test snoc_castSucc
example (i : Fin 2) : Fin.snoc (![10, 20] : Fin 2 → ℕ) 30 i.castSucc = ![10, 20] i := by
  exact Fin.snoc_castSucc 30 ![10, 20] i

-- Test tail
example : Fin.tail (![10, 20, 30] : Fin 3 → ℕ) = (![20, 30] : Fin 2 → ℕ) := by
  exact Fin.tail_cons

-- Test funext
example (f g : Fin 3 → ℕ) (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) : f = g := by
  funext i
  fin_cases i <;> assumption
