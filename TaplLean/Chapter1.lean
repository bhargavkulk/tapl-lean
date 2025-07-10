import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

open Std
open Relation

/-
Formalizing the untyped arithmetic language introduced in 3.1
-/
namespace UntypedArith

/-
t ::=
      true
      false
      if t then t else t
      0
      succ t
      pred t
      is_zero t

This defines the terms of the language.
-/
inductive Term where
  | true
  | false
  | zero
  | succ : Term -> Term
  | pred : Term -> Term
  | is_zero : Term -> Term
  | ite : Term -> Term -> Term -> Term
deriving Repr, DecidableEq

/-
Definition 3.2.1
We then define inductively T, which is the set
of all terms in the language.

- true, false, 0 ∈ T
- if t ∈ T then succ t, pred t, is_zero t ∈ T
- if t₁, t₂, t₃ ∈ T then if t₁ then t₂ else t₃ ∈ T
-/
inductive InT : Term -> Prop where
  | true : InT Term.true
  | false : InT Term.false
  | zero : InT Term.zero
  | succ {t : Term} (H : InT t) : InT (Term.succ t)
  | pred {t : Term} (H : InT t) : InT (Term.pred t)
  | is_zero {t : Term} (H : InT t) : InT (Term.is_zero t)
  | ite {t₁ t₂ t₃ : Term}
        (H₁ : InT t₁) (H₂ : InT t₂) (H₃ : InT t₃) : InT (Term.ite t₁ t₂ t₃)

/- Definition 3.2.3
We can also define the set of all terms differently, building terms
level by level. We call this set S[n], where n is the level.

- S[0] = ∅
- S[i+1] = {true, false, zero}
           ∪ {succ t, pred t, is_zero t | t ∈ S[i]}
           ∪ {if t₁ then t₂ else t₃ | t₁, t₂, t₃ ∈ S[i]}
Finally we can define S.

- S = ⋃ S[i]
-/

inductive InSi : Nat -> Term -> Prop where
  | true {i} : InSi (i + 1) Term.true
  | false {i} : InSi (i + 1) Term.false
  | zero {i} : InSi (i + 1) Term.zero
  | succ {i t} (H : InSi i t) : InSi (i + 1) (Term.succ t)
  | pred {i t} (H : InSi i t) : InSi (i + 1) (Term.pred t)
  | is_zero {i t} (H : InSi i t) : InSi (i + 1) (Term.is_zero t)
  | ite {i t₁ t₂ t₃}
        (H₁ : InSi i t₁) (H₂ : InSi i t₂) (H₃ : InSi i t₃) :
        InSi (i + 1) (Term.ite t₁ t₂ t₃)

def InS (t : Term) : Prop :=
  ∃ i, InSi i t

/-
Exercise 3.2.5
Show that S[i] are cummulative, i.e. S[i] ⊆ S[i+1] for all i.
-/
theorem InSi.cummulative {i t} (H : InSi i t) : InSi (i + 1) t := by
  induction H with
  | true => apply InSi.true
  | false => apply InSi.false
  | zero => apply InSi.zero
  | succ H IH =>
    apply InSi.succ
    assumption
  | pred H IH =>
    apply InSi.pred
    assumption
  | is_zero H IH =>
    apply InSi.is_zero
    assumption
  | ite H₁ H₂ H₃ IH₁ IH₂ IH₃ =>
    apply InSi.ite <;> assumption

/-
We can also prove a more stronger version of the same theorem

∀ i j t, if i <= j and t ∈ S[i]:
  t ∈ S[j]
-/
theorem InSi.monotone {i j t} (H : InSi i t) (Hle : i <= j) : InSi j t := by
  induction Hle with
  | refl => assumption
  | step Hle IH =>
    apply InSi.cummulative
    assumption

/-
Proposition 3.2.6
T = S

My proof is different from the book's proof.
-/
theorem InT.eq_InS {t} : InT t <-> InS t := by
  simp[InS]
  constructor <;> intro H
  -- t ∈ T -> t ∈ S
  · -- Proof follows by induction.
    -- For each case we must find an i such that t ∈ S[i]
    induction H with
    -- true, false, 0 are members of S[1] by definition
    | true =>
      exists 1
      apply InSi.true
    | false =>
      exists 1
      apply InSi.false
    | zero =>
      exists 1
      apply InSi.zero
    | succ H IH => -- we know that there exists i such that H ∈ S[i]
      -- so we can use the same i + 1
      obtain ⟨i, IH⟩ := IH
      exists (i + 1)
      apply InSi.succ
      assumption
    -- pred and zero are similar
    | pred H IH =>
      obtain ⟨i, IH⟩ := IH
      exists (i + 1)
      apply InSi.pred
      assumption
    | is_zero H IH =>
      obtain ⟨i, IH⟩ := IH
      exists (i + 1)
      apply InSi.is_zero
      assumption
    | ite H₁ H₂ H₃ IH₁ IH₂ IH₃ => -- this proof is tricky
      obtain ⟨i₁, IH₁⟩ := IH₁
      obtain ⟨i₂, IH₂⟩ := IH₂
      obtain ⟨i₃, IH₃⟩ := IH₃
      -- we need to construct i such that t₁, t₂, t₃ ∈ S[i]
      -- we also know InSi.monotone
      -- so we the i we need is max(i₁, i₂, i₃)
      let i := max (max i₁ i₂) i₃
      exists (i + 1)
      -- now we need to prove that i₁, i₁, i₂ ≤ i
      -- this will emable us to use InSi.monotone
      have H₁le : i₁ ≤ i := by
        apply Nat.le_trans (m := max i₁ i₂)
        · apply Nat.le_max_left
        · apply Nat.le_max_left
      have H₂le : i₂ ≤ i := by
        apply Nat.le_trans (m := max i₁ i₂)
        · apply Nat.le_max_right
        · apply Nat.le_max_left
      have H₃le : i₃ ≤ i := by
        apply Nat.le_max_right
      apply InSi.ite <;> apply InSi.monotone <;> assumption
  -- t ∈ S -> t ∈ T
  · -- Proof follows by induction.
    obtain ⟨i, H⟩ := H
    induction H with
    -- true, false, zero ∈ T by defintion of T
    | true | false | zero => constructor
    | succ | pred | is_zero => constructor; assumption
    | ite => constructor <;> assumption

/-
Definition 3.3.1

Here we define Const(t), which is the set of all constant terms
appearing in the term t.
-/

def Const (t : Term) : Finset Term :=
  match t with
  | Term.true => {Term.true}
  | Term.false => {Term.false}
  | Term.zero => {Term.zero}
  | Term.succ t => Const t
  | Term.pred t => Const t
  | Term.is_zero t => Const t
  | Term.ite t₁ t₂ t₃ =>
    (Const t₁) ∪ (Const t₂) ∪ (Const t₃)

/-
Definition 3.3.2

We can also define the size(t), which is the size of the term t.
-/

def size (t : Term) : Nat :=
  match t with
  | Term.true => 1
  | Term.false => 1
  | Term.zero => 1
  | Term.succ t => size t + 1
  | Term.pred t => size t + 1
  | Term.is_zero t => size t + 1
  | Term.ite t₁ t₂ t₃ =>
    size t₁ + size t₂ + size t₃ + 1

/-
Definition 3.3.2

We can also define depth(t), which is the depth of the term t.
-/

def depth (t : Term) : Nat :=
  match t with
  | Term.true => 1
  | Term.false => 1
  | Term.zero => 1
  | Term.succ t => depth t + 1
  | Term.pred t => depth t + 1
  | Term.is_zero t => depth t + 1
  | Term.ite t₁ t₂ t₃ =>
    max (max (depth t₁) (depth t₂)) (depth t₃) + 1

/-
We can connect the depth of a term with the set S[i] it belongs to.
depth(t) is the smallest i such that t ∈ S[i].

To prove this we must prove that
- t ∈ S[depth(t)]
- ∀ i, if t ∈ S[i] then depth(t) ≤ i
This is a two-part proof, so we will prove each part separately.
-/
theorem InSi.indexed (t : Term) : InSi (depth t) t := by
  -- both InSi and depth are inductive on t
  -- so proceed by induction on t
  induction t with
  | true | false | zero => simp [depth]; constructor
  | succ | pred | is_zero => simp[depth]; constructor; assumption
  | ite t₁ t₂ t₃ IH₁ IH₂ IH₃ =>
    simp[depth]
    -- tricker proof but proceeds similarly
    -- to the forward part of the proof of InT.eq_InS
    constructor
    · apply InSi.monotone (i := depth t₁)
      · assumption
      · apply Nat.le_max_left
    · apply InSi.monotone (i := depth t₂)
      · assumption
      · apply Nat.le_trans (m := max (depth t₂) (depth t₃))
        · apply Nat.le_max_left
        · apply Nat.le_max_right
    · apply InSi.monotone (i := depth t₃)
      · assumption
      · apply Nat.le_trans (m := max (depth t₂) (depth t₃))
        · apply Nat.le_max_right
        · apply Nat.le_max_right

theorem InSi.depth_minimal (t : Term) (i : Nat) (H : InSi i t) : depth t ≤ i := by
  induction H with
  -- true, false, zero are members of S[1] by definition
  -- their depths are 1
  -- 1 ≤ 1, which makes these cases trivial
  | true | false | zero => simp[depth]
  | succ | pred | is_zero => simp[depth]; assumption
  | ite H₁ H₂ H₃ IH₁ IH₂ IH₃ =>
    simp[depth]
    constructor
    · assumption
    · constructor <;> assumption

/-
Lemma 3.3.3

∀ t, |Consts(t)| ≤ size(t)
-/
lemma Consts.le_size (t : Term) : (Const t).card ≤ size t := by
  induction t <;> simp[Const, size]
  case succ | pred | is_zero => apply Nat.le_succ_of_le; assumption
  case ite t₁ t₂ t₃ IH₁ IH₂ IH₃ =>
    apply Nat.le_succ_of_le
    rw [Nat.add_assoc]
    apply Nat.le_trans (m := (Const t₁).card + (Const t₂ ∪ Const t₃).card)
    · apply Finset.card_union_le
    · apply Nat.add_le_add
      · assumption
      · apply Nat.le_trans (m := (Const t₂).card + (Const t₃).card)
        · apply Finset.card_union_le
        · apply Nat.add_le_add <;> assumption

end UntypedArith

namespace BoolOperationalSemantics

/-
term t ::=
      true
      false
      if t then t else t
-/
inductive Term where
  | true
  | false
  | ite : Term -> Term -> Term -> Term
deriving Repr, DecidableEq

/-
value v ::=
      true
      false
-/
inductive Value : Term -> Prop where
  | true : Value Term.true
  | false : Value Term.false

-- Define a dependent type for values
structure ValueTerm where
  term : Term
  isValue : Value term

/-
Defining t -> t'

─────────────────────────────(IfTrue)
if true then t₂ else t₃ -> t₂

──────────────────────────────(IfFalse)
if false then t₂ else t₃ -> t₃

                  t₁ -> t₁'
───────────────────────────────────────────────(If)
if t₁ then t₂ else t₃ -> if t₁' then t₂ else t₃
-/

inductive Step : Term -> Term -> Prop where
  | IfTrue {t₂ t₃} : Step (Term.ite Term.true t₂ t₃) t₂
  | IfFalse {t₂ t₃} : Step (Term.ite Term.false t₂ t₃) t₃
  | If {t₁ t₁' t₂ t₃} (H : Step t₁ t₁') :
    Step (Term.ite t₁ t₂ t₃) (Term.ite t₁' t₂ t₃)

-- Define notation for the step relation
infix:50 " -b-> " => Step

/-
Definition 3.5.1

An _instance_ of an inference rule is obtained by consistently
replacing each metavariable by the same term in the rule's conclusion.
and all its premises.

Definition 3.5.2

A rule is _satisfied_ by a relation if, for each instance of the rule,
either the conclusion is in the relation or one of the premises is not.

Definition 3.5.3
The one-step evaluation relation → is the smallest binary relation
on terms satisfying the three rules shown. When the pair (t, t′) is
in the evaluation relation, we say that “the evaluation statement (or judgment)
t → t′ is derivable.”
-/

/-
Theorem 3.5.4

The one-step evaluation relation is deterministic,
i.e. if t → t′ and t → t′′, then t′ = t′′.

This proof is tricky, so lets write it down in English first.

We will prove this by induction on the first step t → t'.
1. Case IfTrue:
    This means t -> t' was derived from the rule IfTrue.
    So t = if true then t₂ else t₃, and t' = t₂.
    So we must prove that t'' = t₂.
    We do this by case analysis on t → t''.
    - If t → t'' was derived from IfTrue
      and t = if true then t₂ else t₃,
      then t'' = t₂.
      Which means t' = t''.
    - If t → t'' was derived from IfFalse,
      then t = if false then t₂ else t₃.
      But this is a contradiction,
      because t = if true then t₂ else t₃.
      By the principle of explosion,
      we can conclude that t' = t''.
    - If t → t'' was derived from If,
      t = if t₁ then t₂ else t₃,
      and t' = if t₁' then t₂ else t₃.
      We know already that t = if true then t₂ else t₃,
      so t₁ must be true.
      Therefore true -> t₁' must be true.
      But no such step exists,
      so this case is impossible.
2. Case IfFalse:
    This case is similar to the IfTrue case.
3. Case If:
    If t -> t' was derived from If,
    then there exists t₁ and t₁' such that
    t₁ → t₁'.
    The induction hypothesis states that
    ∀ t₁'', t₁ → t₁'', then t₁' = t₁''.
    We also know that t = if t₁ then t₂ else t₃,
    and t' = if t₁' then t₂ else t₃.
    We case analyze t → t''.
    - If t → t'' was derived from IfTrue,
      then t = if true then t₂ else t₃.
      Which means t₁ = true.
      Which means true -> t₁'.
      But no such step exists,
      so this case is impossible.
    - If t → t'' was derived from IfFalse,
      [Similar to IfTrue]
    - If t → t'' was derived from If,
      [I still don't know how to prove this manually]
-/
theorem Step.unique {t t' t'' : Term} (H₁ : t -b-> t') (H₂ : t -b-> t'') : t' = t'' := by
  induction H₁ generalizing t'' with
  | IfTrue => cases H₂ with
    | IfTrue => rfl
    -- lean discharges IfFalse
    | If H_if => cases H_if
  | IfFalse => cases H₂ with
    | IfFalse => rfl
    -- lean discharges IfTrue
    | If H_if => cases H_if
  | If H_if IH => cases H₂ with
    | IfTrue | IfFalse => cases H_if
    | If H_if' =>
      apply IH at H_if'
      subst H_if'
      rfl

/-
Definition 3.5.6

A term t is in normal form if no evaluation rule applies to it—
i.e., if there is no t′ such that t → t′.
-/

def NormalForm (t : Term) : Prop :=
  ¬ ∃ t', (t -b-> t')

/-
Theorem 3.5.7

Every value is in normal form.
-/
theorem Value.normal_form {v : Term} (H : Value v) : NormalForm v := by
  simp only [NormalForm]
  induction v with
  | true | false => intro ⟨t, H⟩; cases H
  | ite => cases H

/-
Theorem 3.5.8

If t is not a value, then it is not in normal form.
This is contrapositive way of saying if t is in normal form, then it is a value.
-/
theorem normal_forms_are_values {t} (H : ¬ Value t) : ¬ NormalForm t := by
  simp [NormalForm]
  induction t with
  | true | false =>
    exfalso
    apply H
    constructor
  | ite t₁ t₂ t₃ IH₁ IH₂ IH₃ =>
    cases t₁ with
    | true =>
      exists t₂
      constructor
    | false =>
      exists t₃
      constructor
    | ite t₁' t₂' t₃' =>
      -- now we know that the condition is not a value
      -- first we assert
      have H₁_not_value : ¬Value (Term.ite t₁' t₂' t₃') := by
        intro H_val
        cases H_val -- ite cannot be true or false
      -- Apply IH₁ to get a step for the condition
      obtain ⟨t₁_next, H₁_step⟩ := IH₁ H₁_not_value
      exists Term.ite t₁_next t₂ t₃
      constructor
      assumption


inductive MultiStep : Term → Term → Prop
  | refl (x : Term) : MultiStep x x
  | step (x y z : Term) (h : Step x y) (h' : MultiStep y z) : MultiStep x z

infix:50 " ->∗ " => MultiStep

/-
Theorem 3.5.11

[Uniqueness of normal forms]: If t →∗ u and t →∗ u′, where u and u′
are both normal forms, then u = u′.
-/
theorem MultiStep.unique_normal_forms {t u u'}
  (H₁ : t ->∗ u) (H₂ : t ->∗ u')
  (H₃ : NormalForm u) (H₄ : NormalForm u') :
  u = u' := by
  simp [NormalForm] at H₃ H₄
  revert u'
  induction H₁ with
  | refl x =>
    intro u' H₂ H₄
    cases H₂ with
    | refl => rfl
    | step x y z H H' =>
      exfalso
      apply H₃ y
      assumption
  | step x y z H H' IH =>
    intro u' H₂ H₄
    cases H₂ with
    | refl =>
      apply IH <;> try assumption
      exfalso
      apply H₄ y
      assumption
    | step x' y' z' G G' =>
      -- have y_eq : y = y' := Step.unique H G
      apply IH <;> try assumption
      have y_eq : y = y' := Step.unique H G
      subst y_eq
      assumption

/-
A bunch of lemmas to prove Theorem 3.5.12
-/
lemma MultiStep.IfTrue {t₂ t₃ t₂' : Term} (H : t₂ ->∗ t₂') :
  Term.ite Term.true t₂ t₃ ->∗ t₂' := by
  apply MultiStep.step
  · constructor
  · assumption

lemma MultiStep.IfFalse {t₂ t₃ t₃' : Term} (H : t₃ ->∗ t₃') :
  Term.ite Term.false t₂ t₃ ->∗ t₃' := by
  apply MultiStep.step
  · constructor
  · assumption

lemma MultiStep.If {t₁ t₁' t₂ t₃ : Term} (H : t₁ ->∗ t₁') :
  Term.ite t₁ t₂ t₃ ->∗ Term.ite t₁' t₂ t₃ := by
  induction H with
  | refl t₁ =>
    apply MultiStep.refl
  | step t₁ t₂' t₁' H H' IH =>
    apply MultiStep.step (y := t₂'.ite t₂ t₃)
    case h => apply Step.If H
    case h' => assumption

lemma MultiStep.transitive {x y z : Term} (H₁ : MultiStep x y) (H₂ : MultiStep y z) :
  MultiStep x z := by
  induction H₁ with
  | refl => assumption
  | step x' y' z' H H' IH =>
    apply MultiStep.step (y := y')
    case h => assumption
    case h' => apply IH; assumption

/-
Theorem 3.5.12

For every term t there is some normal form t′ such that t →∗ t′.
-/
theorem MultiStep.normal_form (t : Term) :
  ∃ u, NormalForm u ∧ t ->∗ u := by
  simp [NormalForm]
  induction t with
  | true =>
    exists Term.true
    constructor
    · intro x H
      cases H
    · constructor
  | false =>
    exists Term.false
    constructor
    · intro x H
      cases H
    · constructor
  | ite t₁ t₂ t₃ IH₁ IH₂ IH₃ =>
    obtain ⟨u₁, IH₁_nf, IH₁_step⟩ := IH₁
    obtain ⟨u₂, IH₂_nf, IH₂_step⟩ := IH₂
    obtain ⟨u₃, IH₃_nf, IH₃_step⟩ := IH₃
    cases u₁ with
    | true =>
      exists u₂
      constructor
      case left => assumption
      case right =>
        apply MultiStep.transitive (y := Term.ite Term.true t₂ t₃)
        · exact MultiStep.If IH₁_step
        · apply MultiStep.IfTrue
          assumption
    | false =>
      exists u₃
      constructor
      case left => assumption
      case right =>
        apply MultiStep.transitive (y := Term.ite Term.false t₂ t₃)
        · exact MultiStep.If IH₁_step
        · apply MultiStep.IfFalse
          assumption
    | ite t₁' t₂' t₃' =>
      exfalso
      have H_u₁_is_not_value : ¬Value (Term.ite t₁' t₂' t₃') := by
        intro H_val
        cases H_val
      have u₁_not_normal : ¬NormalForm (Term.ite t₁' t₂' t₃') :=
        normal_forms_are_values H_u₁_is_not_value
      simp [NormalForm] at u₁_not_normal
      obtain ⟨t', u₁_not_normal⟩ := u₁_not_normal
      apply IH₁_nf
      apply u₁_not_normal

/-
Exercise 3.5.14

This adapts this exercise to the boolean language.
We just defined the small-step semantics for the boolean language,
but we can also define the big-step semantics.
-/
inductive BigStep : Term -> Term -> Prop where
  | ValueRefl (v: Term) (Hv : Value v) : BigStep v v
  | IfTrue {t₁ t₂ t₃ v₂} (Hv : Value v₂) (Hp : BigStep t₁ Term.true)
    (H : BigStep t₂ v₂) : BigStep (Term.ite Term.true t₂ t₃) v₂
  | IfFalse {t₁ t₂ t₃ v₃} (Hv : Value v₃) (Hp : BigStep t₁ Term.false)
    (H : BigStep t₃ v₃) : BigStep (Term.ite Term.false t₂ t₃) v₃

infix :50 " ⇓ " => BigStep

/-
We can now show that the small-step and big-step semantics coincide.
-/
theorem BigStep.to_Step
  {t v : Term} (H : Value v) : ((MultiStep t v) ↔ (BigStep t v)) := by
  constructor
  -- MultiStep -> BigStep
  · intro H_small_step
    induction H_small_step with
    | refl => constructor; assumption
    | step t₁ t₂ t₃ H_step H_next IH =>
      cases H_step with
      | IfTrue =>
        constructor
        · assumption
        · constructor
          constructor
        apply IH
        assumption
      | IfFalse =>
        constructor
        · assumption
        · constructor
          constructor
        apply IH
        assumption
      | If H_if => sorry
  -- BigStep -> MultiStep
  · intro H_big_step
    induction H_big_step with
    | ValueRefl v Hv => constructor
    | IfTrue H₁ H₂ H₃ H₄ H₅ =>
      apply H₅ at H
      apply MultiStep.IfTrue
      assumption
    | IfFalse H₁ H₂ H₃ H₄ H₅ =>
      apply H₅ at H
      apply MultiStep.IfFalse
      assumption




end BoolOperationalSemantics
