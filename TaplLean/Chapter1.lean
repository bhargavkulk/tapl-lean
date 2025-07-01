import TaplLean.Util

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card


open Std

namespace UArith

inductive Term where
| true : Term
| false : Term
| ite : Term → Term → Term → Term
| zero : Term
| succ : Term → Term
| pred : Term → Term
| is_zero : Term → Term
deriving Repr, DecidableEq

/-
Definition 3.2.1
Following relation defines the set of terms T of the language Term
-/
inductive InT : Term -> Prop where
| true : InT Term.true
| false : InT Term.false
| ite (t1 t2 t3 : Term): InT t1 -> InT t2 -> InT t3 -> InT (Term.ite t1 t2 t3)
| zero : InT Term.zero
| succ {t} : InT t -> InT (Term.succ t)
| pred {t} : InT t -> InT (Term.pred t)
| is_zero {t} : InT t -> InT (Term.is_zero t)

/- Definition 3.2.3
  Step Indexed Relation
  S_0 = ∅ is vacuously false because we cannot construct S 0,
  or construct the proof that any t ∈ S_0

  S i t means the same as t ∈ S_i
-/
inductive S : Nat → Term → Prop
  | true {i} : S (i + 1) Term.true
  | false {i} : S (i + 1) Term.false
  | zero {i} : S (i + 1) Term.zero
  | succ {i} {t} : S i t → S (i + 1) (Term.succ t)
  | pred {i} {t} : S i t → S (i + 1) (Term.pred t)
  | is_zero {i} {t} : S i t → S (i + 1) (Term.is_zero t)
  | ite {i} (t1 t2 t3) : S i t1 → S i t2 → S i t3 → S (i + 1) (Term.ite t1 t2 t3)


def S_u (t : Term) : Prop := ∃ i, S i t

/- Exercise 3.2.5
  S_i ∈ S_i+1
-/
-- curly braces make these values implicit. Lean ill derive from other arguments
theorem S_is_cummulative {i t} (h : S i t) : S (i + 1) t := by
  induction h with
  | true => apply S.true
  | false => apply S.false
  | zero => apply S.zero
  | succ _ IHsucc => apply S.succ IHsucc
  | pred _ IHpred => apply S.pred IHpred
  | is_zero _ IHis_zero => apply S.is_zero IHis_zero
  | ite t1 t2 t3 _ _ _ IH1 IH2 IH3 =>
    apply S.ite
    · assumption
    · assumption
    · assumption
  -- | ite _ _ _ ih1 ih2 ih3 => apply S.ite ih1 ih2 ih3

#print Nat.le
/- A stronger restating of the previous theorem -/
theorem S_monotonic {i j t} (h: S i t) (H: i ≤ j) : S j t := by
  induction H with
  | refl => assumption
  | step k Ihk =>
    apply S_is_cummulative
    assumption

/- Proposition 3.2.6
   T = S
-/

theorem T_eq_S (t : Term) : InT t ↔ S_u t := by
  simp [S_u]
  apply Iff.intro
  -- forward direction
  · intro H
    induction H with
    | true => exact ⟨1, S.true⟩
    | false => exact ⟨1, S.false⟩
    | zero => exact ⟨1, S.zero⟩
    | succ t Ih =>
      obtain ⟨i, Hs⟩ := Ih
      exists (i + 1)
      apply S.succ
      assumption
      -- the previous 3 lines are equivalent to
      -- exact ⟨i + 1, S.succ Hs⟩ OR
    | pred t Ih =>
      obtain ⟨i, Hs⟩ := Ih
      exact ⟨i + 1, S.pred Hs⟩
    | is_zero t Ih =>
      obtain ⟨i, Hs⟩ := Ih
      exact ⟨i + 1, S.is_zero Hs⟩
    | ite t1 t2 t3 H1 H2 H3 IH1 IH2 IH3 =>
      obtain ⟨i1, IH1⟩ := IH1
      obtain ⟨i2, IH2⟩ := IH2
      obtain ⟨i3, IH3⟩ := IH3
      /- we need to construct an i such that
         t1, t2, t3 ∈ S_i
         this is simple, we just take the max of i1, i2 and i3
         and because we know that if i <= j then S_i ⊆ S_j
         then this becomes true -/
      -- So now we prove i1, i2, i3 ≤ max(i1, i2, i3)
      have Hmax3 : i3 ≤ max (max i1 i2) i3 := by
        apply Nat.le_max_right
      have Hmax : max i1 i2 ≤ max (max i1 i2) i3 := by
        apply Nat.le_max_left
      have Hmax1 : i1 ≤ max (max i1 i2) i3 := by
        apply Nat.le_trans ?_ -- could also specify (m := max i1 i2)
        · apply Hmax
        · apply Nat.le_max_left
      have Hmax2 : i2 ≤ max (max i1 i2) i3 := by
        apply Nat.le_trans ?_
        · apply Hmax
        · apply Nat.le_max_right
      let i := max (max i1 i2) i3
      exists i + 1
      apply S.ite
      · apply S_monotonic IH1 Hmax1
      · apply S_monotonic IH2 Hmax2
      · apply S_monotonic IH3 Hmax3
  -- backwards
  · intro H
    obtain ⟨i, H⟩ := H
    induction H with
    | true => apply InT.true
    | false => apply InT.false
    | zero => apply InT.zero
    | succ H IH =>
      apply InT.succ
      assumption
    | pred H IH =>
      apply InT.pred
      assumption
    | is_zero H IH =>
      apply InT.is_zero
      assumption
    | ite t1 t2 t3 H1 H2 H3 IH1 IH2 IH3 =>
      apply InT.ite
      · assumption
      · assumption
      · assumption

/- Definition 3.3.1 -/
inductive Const
  | true
  | false
  | zero
deriving DecidableEq, Repr

def consts : Term → Finset Const
  | Term.true => {Const.true}
  | Term.false => {Const.false}
  | Term.zero => {Const.zero}
  | Term.succ t => consts t
  | Term.pred t => consts t
  | Term.is_zero t => consts t
  | Term.ite t1 t2 t3 =>
    consts t1 ∪ consts t2 ∪ consts t3

def size : Term → Nat
  | Term.true => 1
  | Term.false => 1
  | Term.zero => 1
  | Term.succ t => size t + 1
  | Term.pred t => size t + 1
  | Term.is_zero t => size t + 1
  | Term.ite t1 t2 t3 => size t1 + size t2 + size t3 + 1

/- Lemma 3.3.3
   |consts t| ≤ size t
-/
lemma consts_le_size (t : Term) : Finset.card (consts t) ≤ size t := by
  induction t with
  | true | false | zero => simp [consts, size]
  | succ | pred | is_zero =>
    simp [consts, size]
    apply Nat.le_succ_of_le
    assumption
  | ite t1 t2 t3 IH1 IH2 IH3 =>
    simp [consts, size]
    apply Nat.le_succ_of_le
    apply Nat.le_trans
    · apply Finset.card_union_le
    rw [Nat.add_assoc]
    apply Nat.add_le_add
    · assumption
    · apply Nat.le_trans
      · apply Finset.card_union_le
      apply Nat.add_le_add
      · assumption
      · assumption

end UArith

namespace UBool

inductive Term where
  | true : Term
  | false : Term
  | ite : Term → Term → Term → Term
deriving DecidableEq, Repr

inductive Value : Term → Prop where
  | true : Value Term.true
  | false : Value Term.false

/- Fig 3-1
   Operational Semantics of Boolean Terms
-/
inductive BStep : Term → Term → Prop
  | EIfTrue {t1 t2} :
      BStep (Term.ite Term.true t1 t2) t1
  | EIfFalse {t1 t2} :
      BStep (Term.ite Term.false t1 t2) t2
  | EIf {t1 t1' t2 t3} :
      BStep t1 t1' →
      BStep (Term.ite t1 t2 t3) (Term.ite t1' t2 t3)

instance : StepRel Term where
  step := BStep

/- Theorem 3.5.4 [Determinancy of One-Step Evaluation] -/
theorem step_is_deterministic {t t' t'' : Term} (H1 : t -> t') (H2 : t -> t'')
  : t' = t'' := by
  induction H1 generalizing t'' with
  | EIfTrue =>
    cases H2 with
    | EIfTrue => rfl
    | EIf Hs => cases Hs
  | EIfFalse =>
    cases H2 with
    | EIfFalse => rfl
    | EIf Hs => cases Hs
  | EIf Hs IHs =>
    cases H2 with
    | EIfTrue => cases Hs
    | EIfFalse => cases Hs
    | EIf Hs' =>
      have H := IHs Hs'
      simp [H]

/- Definition 3.5.6 -/
def NormalForm (t : Term) : Prop :=
  ¬ ∃ t', t -> t'

/- Theorem 3.5.7 Every value is normal form -/
theorem values_are_normal_forms {t} (Hv : Value t) : NormalForm t := by
  simp [NormalForm]
  intro t'
  intro H
  induction Hv with
  | true =>
    cases H
  | false =>
    cases H

/- 3.5.8 Theorem: If t is in normal form, then t is a value -/
theorem normal_forms_are_values {t} (Hv : ¬ Value t) : ¬ NormalForm t := by
  simp [NormalForm]
  induction t with
  | true =>
    exfalso
    apply Hv
    apply Value.true
  | false =>
    exfalso
    apply Hv
    apply Value.false
  | ite t1 t2 t3 IH1 IH2 IH3 =>
    by_cases HTrue : t1 = Term.true
    · subst HTrue
      exists t2
      apply BStep.EIfTrue
    by_cases HFalse : t1 = Term.false
    · subst HFalse
      exists t3
      apply BStep.EIfFalse
    have Hv' : ¬ Value t1 := by
      intro Hv'
      cases Hv' <;> contradiction
    obtain ⟨t1', Hs⟩ := IH1 Hv'
    exists t1'.ite t2 t3
    apply BStep.EIf
    assumption

inductive MultiStep : Term → Term → Prop
| refl (x : Term) : MultiStep x x
| step (x y z : Term) (h : BStep x y) (h' : MultiStep y z) : MultiStep x z

infixr:50 " ->* " => MultiStep


lemma multi_step (x y : Term) (H: x -> y) : x ->* y := by
  apply MultiStep.step (y := y)
  · assumption
  · apply MultiStep.refl

lemma multi_trans (x y z: Term) (H1: x ->* y) (H2: y ->* z) : x ->* z := by
  induction H1 with
  | refl x => assumption
  | step x' y' z' H H' IH =>
    have IH := IH H2
    apply MultiStep.step (y := y') <;> assumption

/- 3.5.11 Theorem [Uniqueness of normal forms]: If t -→∗ u and t -→∗ u′, where u
and u′ are both normal forms, then u = u′. -/
theorem uniqueness_of_normal_forms {x y1 y2 : Term}
  (H : x ->* y1)
  (H' : x ->* y2)
  (Hn : NormalForm y1)
  (Hn' : NormalForm y2) :
  y1 = y2 := by
  revert y2 -- copied from software foundations kek
  induction H with
  | refl x =>
    intro y2 H Hnf
    cases H with
    | refl => rfl
    | step x' y' z' => -- contradiction here somehow
      exfalso
      apply Hn
      exists y'
  | step x' y' z' H H' IH =>
    intro y2 Hs Hn'
    cases Hs with
    | refl => -- contradiction here too
      exfalso
      apply Hn'
      exists y'
    | step x'' y'' z'' =>
      apply IH -- no clue what happened here, vibes
      · assumption
      · have Heq: y' = y'' := by
          apply step_is_deterministic (t := x') <;> assumption
        simp [Heq]
        assumption
      · assumption

/- 3.5.12 Theorem [Termination of Evaluation]:
  For every term t there is some normal form t′ such that t →∗ t′.  -/
-- might need some auxilary lemmas
/- lemma multistep_congr_cond :
    ∀ t1 t1' t2 t3,
    t1 ->* t1' →
    Term.ite t1 t2 t3 ->* Term.ite t1' t2 t3 := by
  intro t1 t1' t2 t3 H
  induction H with
  | refl => apply MultiStep.refl
  | step t t' t'' H H' IH =>
    apply MultiStep.step (y := t'.ite t2 t3)
    · apply BStep.EIf
      assumption
    · assumption -/

-- not sure how to prove this, or whether our semantics allow this
theorem termination_of_evaluation :
  ∀ t, ∃ t', t ->* t' ∧ NormalForm t' := by
  intro t
  induction t with
  -- true / false are trivially true because they are already
  -- normal forms
  | true =>
    exists Term.true
    constructor
    · apply MultiStep.refl
    · simp [NormalForm]
      intro x H
      cases H
  | false =>
    exists Term.false
    constructor
    · apply MultiStep.refl
    · simp [NormalForm]
      intro x H
      cases H
  -- trickier case
  | ite t1 t2 t3 IH1 IH2 IH3 => sorry

end UBool
