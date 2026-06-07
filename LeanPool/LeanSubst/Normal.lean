/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import Init.WF
import LeanPool.LeanSubst.Ren
import LeanPool.LeanSubst.Subst
import LeanPool.LeanSubst.Reduction

namespace LeanSubst
  universe u

  section
    variable {T : Type}

    def Reducible (R : T -> T -> Prop) (t : T) := ∃ t', R t t'
    def Normal (R : T -> T -> Prop) (t : T) := ¬ (Reducible R t)
    def NormalForm (R : T -> T -> Prop) (t : T) (t' : T) := Star R t t' ∧ Normal R t'
    def WN (R : T -> T -> Prop) (t : T) := ∃ t', NormalForm R t t'

    inductive SN (R : T -> T -> Prop) : T -> Prop where
    | sn {x} : (∀ y, R x y -> SN R y) -> SN R x

    inductive SNPlus (R : T -> T -> Prop) : T -> Prop where
    | sn {x} : (∀ y, Plus R x y -> SNPlus R y) -> SNPlus R x

    variable {R R1 R2 : T -> T -> Prop}

    namespace SNPlus
      theorem impies_sn {t} : SNPlus R t -> SN R t := by
        intro h; induction h; case _ t' _ ih =>
        constructor; intro t'' r
        apply ih t'' (Plus.start r)

      theorem preservation_step {t t'} : SNPlus R t -> R t t' -> SNPlus R t' := by
        intro h r; induction h; case _ z h _ =>
          apply h _ (Plus.start r)

      theorem preservation {t t'} : SNPlus R t -> Star R t t' -> SNPlus R t' := by
        intro h r; induction r
        case _ => apply h
        case _ _ r2 ih =>
          apply preservation_step ih r2
    end SNPlus

    namespace SN
      theorem preimage (f : T -> T) x :
        (∀ x y, R x y -> R (f x) (f y)) ->
        SN R (f x) ->
        SN R x
      := by
        intro h sh
        generalize zdef : f x = z at sh
        induction sh generalizing f x
        case _ x' h' ih =>
          subst zdef; constructor
          intro y r
          apply ih (f y) (h _ _ r) f y h rfl

      theorem preservation_step {t t'} : SN R t -> R t t' -> SN R t' := by
        intro h red
        induction h
        case _ z h1 _h2 =>
          apply h1 _ red

      theorem preservation {t t'} : SN R t -> Star R t t' -> SN R t' := by
        intro h red
        induction red
        case _ => simp [*]
        case _ _ r2 ih => apply preservation_step ih r2

      theorem star {t} : (∀ y, Star R t y -> SN R y) -> SN R t := by
        intro h
        constructor
        intro y r
        apply h y (Star.step Star.refl r)

      theorem implies_snplus {t} : SN R t -> SNPlus R t := by
        intro h; induction h; case _ t' _ ih =>
        constructor; intro t'' r
        have lem := Plus.destruct r
        cases lem; case _ z lem =>
          have lem2 := ih z lem.1
          apply SNPlus.preservation lem2 lem.2

      theorem expansion_step {t t' : T} (f : FunctionalTerm R t) : SN R t' -> R t t' -> SN R t := by
        intro h r
        apply SN.sn; intro y r'
        rw [<-f r r']
        apply h

      theorem expansion {t t' : T} [Functional R] : SN R t' -> Star R t t' -> SN R t := by
        intro h r
        induction r; apply h
        case _ r1 r2 ih =>
          have lem := expansion_step Functional.functional h r2
          apply ih lem

      theorem equiv_acc {t} : SN R t <-> Acc (flip $ R) t := by
        apply Iff.intro
        case _ =>
          intro h; induction h
          case _ x h ih =>
          constructor
          simp [flip]
          exact ih
        case _ =>
          intro h; induction h
          case _ x h ih =>
          constructor
          simp [flip] at ih
          exact ih

      theorem wellfounded : (∀ t, SN R t) -> WellFounded (flip $ R) := by
        intro h; constructor
        intro a; replace h := h a
        apply equiv_acc.1 h

      variable [RenMap T] [SubstMap T T] [Substitutive R]

      theorem subst_preimage {σ : Subst T} {t} : SN R t[σ] -> SN R t := by
        intro r; apply preimage (smap σ) t _ r
        intro x y r; apply Substitutive.subst
        apply r
    end SN
  end
end LeanSubst
