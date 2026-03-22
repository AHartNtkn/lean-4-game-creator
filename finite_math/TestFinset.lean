import Game.Metadata

-- Is tauto available from current imports (no Finset)?
example : True ∨ False := by tauto
example (P Q : Prop) (h : P) : P ∨ Q := by tauto
