/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StdTransport
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.CircleValue

/-!
# The circle value in the model

The composite of the coevaluation and evaluation classes is the
free circle: gluing the two strand ends creates exactly one free
circle, so the categorical scalar of `η_ ≫ ε_` is the circle
value of the parameter.  Transporting through the fibre functor
and the standard model identifies it with the superdimension
`k − 2ℓ`.
-/

@[expose] public section

namespace RS

open CategoryTheory Functor.LaxMonoidal Functor.OplaxMonoidal
open MonoidalCategory

/-- The circle composite has no flags: both strand ends are
glued. -/
theorem circleCompose_flag_empty :
    IsEmpty (coevFrag.compose evFrag).Flag := by
  constructor
  intro g
  obtain ⟨⟨y, hy1, hy2⟩, hx1, hx2⟩ := g
  rcases y with i | i <;>
    rcases (show i = ⟨0, Nat.zero_lt_two⟩ ∨
        i = ⟨1, Nat.one_lt_two⟩ from by
      have h2 := i.isLt
      rcases Nat.lt_or_ge i.val 1 with h | h
      · exact Or.inl (Fin.ext (show i.val = 0 by omega))
      · exact Or.inr (Fin.ext (show i.val = 1 by omega)))
      with rfl | rfl
  · exact hx1 (Subtype.ext rfl)
  · exact hy1 rfl
  · exact hx2 (Subtype.ext rfl)
  · exact hy2 rfl

/-- **The strand closure is the free circle.** -/
noncomputable def circleComposeEquiv :
    (coevFrag.compose evFrag).Equiv (circlesClosed 1) where
  flagEquiv :=
    haveI := circleCompose_flag_empty
    haveI : IsEmpty (circlesClosed 1).Flag :=
      inferInstanceAs (IsEmpty Empty)
    _root_.Equiv.equivOfIsEmpty _ _
  vertexEquiv :=
    haveI : IsEmpty (coevFrag.compose evFrag).Vertex :=
      ⟨fun v => by rcases v with w | w <;> exact w.elim⟩
    haveI : IsEmpty (circlesClosed 1).Vertex :=
      inferInstanceAs (IsEmpty Empty)
    _root_.Equiv.equivOfIsEmpty _ _
  attach_comm := fun g =>
    haveI := circleCompose_flag_empty
    isEmptyElim g
  pairing_comm := fun g =>
    haveI := circleCompose_flag_empty
    isEmptyElim g
  circles_eq := rfl

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **The categorical circle**: composing coevaluation and
evaluation is the circle value times the identity. -/
theorem coev_comp_ev :
    (η_ (SkeinObj.mk 1 : SkeinObj f) (SkeinObj.mk 1) ≫
        ε_ (SkeinObj.mk 1) (SkeinObj.mk 1) :
      (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk 0) =
      circleVal f • 𝟙 (SkeinObj.mk 0) := by
  change HomSpace.comp f 0 2 0 (coevClass f) (evClass f) = _
  rw [coevClass, evClass, HomSpace.comp_ofFragment]
  rw [HomSpace.ofFragment_congr f circleComposeEquiv]
  rw [show HomSpace.ofFragment f.val (circlesClosed 1) =
      f.val (circlesClosed 1) •
        HomSpace.ofFragment f.val emptyClosedFragment from
    ofFragment_eq_smul_empty f (circlesClosed 1)]
  rw [empty_class_eq_id]
  rfl

variable (P : DelignePackage (SkeinObj f))

-- The circle value is read off the standard form
-- and copairing, both of which unfold over the even and odd
-- blocks of the model.
/-- **The circle value is the superdimension** `k − 2ℓ` under any
standard-model identification. -/
theorem circleVal_model {k ℓ : ℕ}
    (e : SuperVect.Hom (stdSuperPair k ℓ) (P.ω.obj (SkeinObj.mk 1)))
    (e' : SuperVect.Hom (P.ω.obj (SkeinObj.mk 1)) (stdSuperPair k ℓ))
    (hee' : SuperVect.Hom.comp e e' =
      SuperVect.Hom.id (P.ω.obj (SkeinObj.mk 1)))
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ)
    (hcopair :
      letI := P.braided
      SuperVect.Hom.comp (SuperVect.tensorHom e' e')
        (ε P.ω ≫ P.ω.map (η_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫
          δ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) =
        stdCopair k ℓ) :
    circleVal f = (k : ℂ) - 2 * ℓ := by
  let := P.braided
  -- The categorical scalar of the circle is the circle value.
  have hcirc : ((ε P.ω ≫ P.ω.map
      (η_ (SkeinObj.mk 1 : SkeinObj f) (SkeinObj.mk 1) ≫
        ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω :
      SuperVect.tensorUnit ⟶ SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap 1 = circleVal f := by
    rw [coev_comp_ev f]
    rw [show P.ω.map (circleVal f • 𝟙 (SkeinObj.mk 0)) =
        circleVal f • 𝟙 (P.ω.obj (SkeinObj.mk 0)) from
      (P.linear.map_smul _ _).trans
        (by rw [CategoryTheory.Functor.map_id])]
    rw [CategoryTheory.Linear.smul_comp,
      CategoryTheory.Linear.comp_smul]
    rw [show (𝟙 (P.ω.obj (SkeinObj.mk 0)) ≫ η P.ω :
        P.ω.obj (SkeinObj.mk 0) ⟶ SuperVect.tensorUnit) =
      η P.ω from CategoryTheory.Category.id_comp _]
    rw [show (ε P.ω ≫ η P.ω : SuperVect.tensorUnit ⟶
        SuperVect.tensorUnit) = 𝟙 _ from
      Functor.Monoidal.ε_η P.ω]
    change circleVal f * 1 = circleVal f
    ring
  -- The same scalar through the standard model.
  have hsplit : ((ε P.ω ≫ P.ω.map
      (η_ (SkeinObj.mk 1 : SkeinObj f) (SkeinObj.mk 1) ≫
        ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω :
      SuperVect.tensorUnit ⟶ SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap 1 =
      (SuperVect.Hom.comp (stdForm k ℓ) (stdCopair k ℓ)).evenMap
        1 := by
    have hmap : P.ω.map
        (η_ (SkeinObj.mk 1 : SkeinObj f) (SkeinObj.mk 1) ≫
          ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) =
        P.ω.map (η_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) :=
      P.ω.map_comp _ _
    have hmid : (δ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
        μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) :
        P.ω.obj (SkeinObj.mk 2) ⟶ P.ω.obj (SkeinObj.mk 2)) =
        𝟙 _ :=
      Functor.Monoidal.δ_μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)
    have hins : (δ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          ((e' ⊗ₘ e') ≫ (e ⊗ₘ e)) ≫
            μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) :
        P.ω.obj (SkeinObj.mk 2) ⟶ P.ω.obj (SkeinObj.mk 2)) =
        𝟙 _ := by
      rw [show ((e' ⊗ₘ e') ≫ (e ⊗ₘ e) :
          P.ω.obj (SkeinObj.mk 1) ⊗ P.ω.obj (SkeinObj.mk 1) ⟶
            P.ω.obj (SkeinObj.mk 1) ⊗
              P.ω.obj (SkeinObj.mk 1)) = 𝟙 _ from by
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
        rw [show (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
            P.ω.obj (SkeinObj.mk 1)) = 𝟙 _ from hee']
        exact MonoidalCategory.id_tensorHom_id _ _]
      rw [CategoryTheory.Category.id_comp]
      exact hmid
    rw [hmap]
    rw [show (P.ω.map (η_ (SkeinObj.mk 1 : SkeinObj f)
          (SkeinObj.mk 1)) ≫
        P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) :
        P.ω.obj (SkeinObj.mk 0) ⟶ P.ω.obj (SkeinObj.mk 0)) =
      P.ω.map (η_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫
        (δ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          ((e' ⊗ₘ e') ≫ (e ⊗ₘ e)) ≫
            μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) from by
      rw [hins]
      exact (congrArg (fun z : P.ω.obj (SkeinObj.mk 2) ⟶
          P.ω.obj (SkeinObj.mk 0) =>
        P.ω.map (η_ (SkeinObj.mk 1 : SkeinObj f)
          (SkeinObj.mk 1)) ≫ z)
        (CategoryTheory.Category.id_comp
          (P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1))))).symm]
    rw [← hform, ← hcopair]
    rfl
  rw [← hcirc, hsplit]
  exact stdForm_comp_stdCopair k ℓ

end RS
