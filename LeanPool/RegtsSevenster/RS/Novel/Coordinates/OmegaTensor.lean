/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarTensorClass

/-!
# Image vectors of tensors

The fibre functor sends tensor products of point morphisms to
the structure-map image of the tensor of their image vectors.
The coherence is proved abstractly for any monoidal functor —
where every rewrite fires — and the strictness of the skein unit
is exploited only in two small concrete bridging steps.
-/

namespace RS

open CategoryTheory Functor.LaxMonoidal Functor.OplaxMonoidal
open MonoidalCategory

/-- The even component of a tensor of even vectors. -/
def evenPair {V W : SuperVect} (v : V.even) (w : W.even) :
    (SuperVect.tensorObj V W).even := (v ⊗ₜ[ℂ] w, 0)

/-- **Points are monoidal**: for a monoidal functor, the counit
composed with the image of a corrected tensor of points is the
tensor of the point images assembled by the structure map. -/
theorem point_tensor {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {A B : C}
    (p : 𝟙_ C ⟶ A) (q : 𝟙_ C ⟶ B) :
    ε F ≫ F.map ((λ_ (𝟙_ C)).inv ≫ (p ⊗ₘ q)) =
      (λ_ (𝟙_ D)).inv ≫
        ((ε F ≫ F.map p) ⊗ₘ (ε F ≫ F.map q)) ≫ μ F A B := by
  rw [F.map_comp, Functor.Monoidal.map_leftUnitor_inv]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural]
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
  rw [← MonoidalCategory.tensorHom_def'_assoc]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The inverse left unitor of the skein category at the unit is
the identity. -/
theorem skein_leftUnitor_unit_inv :
    (λ_ (𝟙_ (SkeinObj f))).inv = 𝟙 (𝟙_ (SkeinObj f)) := by
  change bundleMapClass f (finCongr _) = _
  rw [show (finCongr (show (0 : ℕ) = 0 + 0 by omega) :
      Fin 0 ≃ Fin (0 + 0)) = _root_.Equiv.refl (Fin 0) from
    _root_.Equiv.ext (fun x => Fin.ext rfl)]
  exact bundleMapClass_refl f 0

variable (P : DelignePackage (SkeinObj f))

/-- The image vector of a composite: apply the image of the
second factor. -/
theorem omegaVec_comp {a b : ℕ}
    (p : (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk a)
    (q : (SkeinObj.mk a : SkeinObj f) ⟶ SkeinObj.mk b) :
    omegaVec f P (p ≫ q) =
      (P.ω.map q).evenMap (omegaVec f P p) := by
  let := P.braided
  change ((ε P.ω ≫ P.ω.map (p ≫ q) : SuperVect.tensorUnit ⟶
      P.ω.obj (SkeinObj.mk b)) :
    SuperVect.Hom _ _).evenMap 1 = _
  rw [P.ω.map_comp]
  rfl

/-- The image vector is homogeneous in the morphism. -/
theorem omegaVec_smul {a : ℕ} (r : ℂ)
    (p : (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk a) :
    omegaVec f P (r • p) = r • omegaVec f P p := by
  let := P.braided
  change ((ε P.ω ≫ P.ω.map (r • p) : SuperVect.tensorUnit ⟶
      P.ω.obj (SkeinObj.mk a)) :
    SuperVect.Hom _ _).evenMap 1 = _
  rw [show P.ω.map (r • p) = r • P.ω.map p from
    P.linear.map_smul p r,
    CategoryTheory.Linear.comp_smul]
  rfl

/-- The tensor of morphisms on an even pair acts
componentwise. -/
theorem tensorHom_evenPair {V₁ V₂ W₁ W₂ : SuperVect}
    (g : V₁ ⟶ V₂) (h : W₁ ⟶ W₂) (v : V₁.even) (w : W₁.even) :
    ((g ⊗ₘ h : SuperVect.tensorObj V₁ W₁ ⟶
        SuperVect.tensorObj V₂ W₂) :
      SuperVect.Hom _ _).evenMap (evenPair v w) =
      evenPair ((g : SuperVect.Hom _ _).evenMap v)
        ((h : SuperVect.Hom _ _).evenMap w) := by
  change (SuperVect.tensorHom g h).evenMap (evenPair v w) = _
  change ((TensorProduct.map (g : SuperVect.Hom _ _).evenMap
        (h : SuperVect.Hom _ _).evenMap) (v ⊗ₜ[ℂ] w),
    (TensorProduct.map (g : SuperVect.Hom _ _).oddMap
        (h : SuperVect.Hom _ _).oddMap) 0) = _
  rw [TensorProduct.map_tmul, map_zero]
  rfl

/-- The inverse left unitor of `SuperVect` at the unit sends `1`
to the even pair of units. -/
theorem superVect_leftUnitor_inv_one :
    (((λ_ (𝟙_ SuperVect)).inv : SuperVect.tensorUnit ⟶
        SuperVect.tensorObj SuperVect.tensorUnit
          SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap (1 : ℂ) =
      evenPair (1 : ℂ) (1 : ℂ) := by
  change (LinearMap.inl ℂ _ _ ∘ₗ
    (TensorProduct.lid ℂ ℂ).symm.toLinearMap) 1 = _
  rw [LinearMap.comp_apply]
  rw [show (TensorProduct.lid ℂ ℂ).symm.toLinearMap (1 : ℂ) =
    (1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) from TensorProduct.lid_symm_apply 1]
  rfl

-- Raised budget: monoidality of the image vector unfolds the
-- tensorator and the left unitor on both sides.
/-- **Image vectors are monoidal**: the image vector of a tensor
of point morphisms is the structure-map image of the even pair
of the image vectors. -/
theorem omegaVec_tensor {a b : ℕ}
    (p : (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk a)
    (q : (SkeinObj.mk 0 : SkeinObj f) ⟶ SkeinObj.mk b) :
    let _ := P.braided
    omegaVec f P (d := a + b) (HomSpace.tensor f 0 a 0 b p q) =
      ((μ P.ω (SkeinObj.mk a) (SkeinObj.mk b)) :
        SuperVect.Hom _ _).evenMap
        (evenPair (omegaVec f P p) (omegaVec f P q)) := by
  let _ := P.braided
  have hskein : ((λ_ (𝟙_ (SkeinObj f))).inv ≫ (p ⊗ₘ q) :
      𝟙_ (SkeinObj f) ⟶
        SkeinObj.mk a ⊗ SkeinObj.mk b) = p ⊗ₘ q := by
    rw [skein_leftUnitor_unit_inv]
    exact Category.id_comp _
  have habs := point_tensor P.ω p q
  rw [hskein] at habs
  have hev := congrArg
    (fun z : (𝟙_ SuperVect ⟶
        P.ω.obj (SkeinObj.mk a ⊗ SkeinObj.mk b)) =>
      (z : SuperVect.Hom _ _).evenMap (1 : ℂ)) habs
  refine Eq.trans hev ?_
  change ((μ P.ω (SkeinObj.mk a) (SkeinObj.mk b)) :
      SuperVect.Hom _ _).evenMap
    ((((ε P.ω ≫ P.ω.map p) ⊗ₘ (ε P.ω ≫ P.ω.map q) :
        SuperVect.tensorObj SuperVect.tensorUnit
          SuperVect.tensorUnit ⟶ _) :
      SuperVect.Hom _ _).evenMap
      ((((λ_ (𝟙_ SuperVect)).inv : SuperVect.tensorUnit ⟶
          SuperVect.tensorObj SuperVect.tensorUnit
            SuperVect.tensorUnit) :
        SuperVect.Hom _ _).evenMap (1 : ℂ))) = _
  rw [superVect_leftUnitor_inv_one, tensorHom_evenPair]
  rfl

end RS
