-- Util.lean

universe u

class StepRel (α : Type u) where
  step : α → α → Prop

infixr:50 " -> " => StepRel.step
