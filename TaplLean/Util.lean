-- Util.lean

universe u

class StepRel (α : Type u) where
  step : α → α → Prop

infixr:50 " -> " => StepRel.step

inductive MultiStep {α : Type u} [inst : StepRel α] : α → α → Prop where
  | refl {t} : MultiStep t t
  | step {t t'} (h : StepRel.step t t') : MultiStep t t'
  | trans {t t' t''} (h₁ : MultiStep t t') (h₂ : MultiStep t' t'') : MultiStep t t''

infixr:50 " ->* " => MultiStep
