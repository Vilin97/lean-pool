/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaStarVec

/-!
# Image functionals of tensors

The dual of the point-tensor coherence: the fibre functor sends
tensor products of copoint morphisms to the product of their
image functionals through the structure map.  Abstract coherence
first — every rewrite fires over generic instances — then the
strict skein unit and the concrete SuperVect unitor.
-/

@[expose] public section

namespace RS

open CategoryTheory Functor.LaxMonoidal Functor.OplaxMonoidal
open MonoidalCategory

/-- **Copoints are monoidal**: for a monoidal functor, the
structure map followed by the image of a corrected tensor of
copoints and the unit map is the tensor of the copoint images
followed by the target unitor. -/
theorem point_cotensor {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {A B : C}
    (q₁ : A ⟶ 𝟙_ C) (q₂ : B ⟶ 𝟙_ C) :
    μ F A B ≫ F.map ((q₁ ⊗ₘ q₂) ≫ (λ_ (𝟙_ C)).hom) ≫ η F =
      ((F.map q₁ ≫ η F) ⊗ₘ (F.map q₂ ≫ η F)) ≫
        (λ_ (𝟙_ D)).hom := by
  rw [F.map_comp]
  rw [show μ F A B ≫ (F.map (q₁ ⊗ₘ q₂) ≫
      F.map (λ_ (𝟙_ C)).hom) ≫ η F =
    (μ F A B ≫ F.map (q₁ ⊗ₘ q₂)) ≫
      F.map (λ_ (𝟙_ C)).hom ≫ η F from by
    simp only [Category.assoc]]
  rw [← Functor.LaxMonoidal.μ_natural]
  rw [Functor.Monoidal.map_leftUnitor]
  simp only [Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [show (λ_ (F.obj (𝟙_ C))).hom ≫ η F =
      (𝟙_ D ◁ η F) ≫ (λ_ (𝟙_ D)).hom from
    (MonoidalCategory.leftUnitor_naturality (η F)).symm]
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (fun z => z ≫ (λ_ (𝟙_ D)).hom) ?_
  rw [← MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.comp_id]

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))

/-- The tensor of functionals on an even pair evaluates to the
product. -/
theorem lambda_evenPair {V W : SuperVect}
    (g : V ⟶ SuperVect.tensorUnit)
    (h : W ⟶ SuperVect.tensorUnit) (v : V.even) (w : W.even) :
    (((g ⊗ₘ h : SuperVect.tensorObj V W ⟶
        SuperVect.tensorObj SuperVect.tensorUnit
          SuperVect.tensorUnit) ≫
      (λ_ (𝟙_ SuperVect)).hom : SuperVect.tensorObj V W ⟶
        SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap (evenPair v w) =
      (g : SuperVect.Hom _ _).evenMap v *
        (h : SuperVect.Hom _ _).evenMap w := by
  change ((λ_ (𝟙_ SuperVect)).hom : SuperVect.Hom _ _).evenMap
    ((SuperVect.tensorHom g h).evenMap (evenPair v w)) = _
  rw [show (SuperVect.tensorHom g h).evenMap (evenPair v w) =
      evenPair ((g : SuperVect.Hom _ _).evenMap v)
        ((h : SuperVect.Hom _ _).evenMap w) from
    tensorHom_evenPair g h v w]
  change (TensorProduct.lid ℂ ℂ).toLinearMap
    ((LinearMap.fst ℂ _ _)
      (evenPair ((g : SuperVect.Hom _ _).evenMap v)
        ((h : SuperVect.Hom _ _).evenMap w))) = _
  rw [show (LinearMap.fst ℂ _ _)
      (evenPair ((g : SuperVect.Hom _ _).evenMap v)
        ((h : SuperVect.Hom _ _).evenMap w)) =
    ((g : SuperVect.Hom _ _).evenMap v) ⊗ₜ[ℂ]
      ((h : SuperVect.Hom _ _).evenMap w) from rfl]
  exact TensorProduct.lid_tmul _ _

-- Monoidality of the image functional unfolds the
-- tensorator and both unitors on each block.
/-- **Image functionals are monoidal**: the image functional of a
tensor of copoint morphisms, evaluated on a structure-map image
of an even pair, is the product of the image functionals. -/
theorem omegaFun_tensor {a b : ℕ}
    (q₁ : (SkeinObj.mk a : SkeinObj f) ⟶ SkeinObj.mk 0)
    (q₂ : (SkeinObj.mk b : SkeinObj f) ⟶ SkeinObj.mk 0)
    (v : (P.ω.obj (SkeinObj.mk a)).even)
    (w : (P.ω.obj (SkeinObj.mk b)).even) :
    letI := P.braided
    omegaFun f P (q₁ ⊗ₘ q₂)
        (((μ P.ω (SkeinObj.mk a) (SkeinObj.mk b)) :
          SuperVect.Hom _ _).evenMap (evenPair v w)) =
      omegaFun f P q₁ v * omegaFun f P q₂ w := by
  let := P.braided
  have hhom : (λ_ (𝟙_ (SkeinObj f))).hom =
      𝟙 (𝟙_ (SkeinObj f)) := by
    have h1 := Iso.hom_inv_id (λ_ (𝟙_ (SkeinObj f)))
    rw [skein_leftUnitor_unit_inv, Category.comp_id] at h1
    exact h1
  have hskein : ((q₁ ⊗ₘ q₂) ≫
      (λ_ (𝟙_ (SkeinObj f))).hom :
      SkeinObj.mk a ⊗ SkeinObj.mk b ⟶ 𝟙_ (SkeinObj f)) =
      q₁ ⊗ₘ q₂ := by
    rw [hhom]
    exact Category.comp_id _
  have habs := point_cotensor P.ω q₁ q₂
  rw [hskein] at habs
  have hev := congrArg
    (fun z : (P.ω.obj (SkeinObj.mk a) ⊗
        P.ω.obj (SkeinObj.mk b) ⟶ 𝟙_ SuperVect) =>
      (z : SuperVect.Hom _ _).evenMap (evenPair v w)) habs
  refine Eq.trans ?_ (Eq.trans hev ?_)
  · rfl
  · change ((((P.ω.map q₁ ≫ η P.ω) ⊗ₘ (P.ω.map q₂ ≫ η P.ω)) ≫
        (λ_ (𝟙_ SuperVect)).hom :
        P.ω.obj (SkeinObj.mk a) ⊗ P.ω.obj (SkeinObj.mk b) ⟶
          SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap (evenPair v w) = _
    exact lambda_evenPair (P.ω.map q₁ ≫ η P.ω)
      (P.ω.map q₂ ≫ η P.ω) v w

/-- The image functional of a composite: precompose with the
image of the first factor. -/
theorem omegaFun_comp {a b : ℕ}
    (p : (SkeinObj.mk a : SkeinObj f) ⟶ SkeinObj.mk b)
    (q : (SkeinObj.mk b : SkeinObj f) ⟶ SkeinObj.mk 0)
    (v : (P.ω.obj (SkeinObj.mk a)).even) :
    omegaFun f P (p ≫ q) v =
      omegaFun f P q ((P.ω.map p).evenMap v) := by
  let := P.braided
  change ((P.ω.map (p ≫ q) ≫ η P.ω : P.ω.obj (SkeinObj.mk a) ⟶
      SuperVect.tensorUnit) :
    SuperVect.Hom _ _).evenMap v = _
  rw [P.ω.map_comp]
  rfl

end RS
