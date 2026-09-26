/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapSplit

/-!
# Odd pairs and their vanishing under split functionals

The odd⊗odd block of a tensor lands in the even part; under a
tensor of copoint functionals it vanishes, because copoints kill
odd parts (the unit has no odd part).  This disposes of the
cross-split odd basis terms in the cap recursion.
-/

@[expose] public section

namespace RS

open CategoryTheory Functor.LaxMonoidal Functor.OplaxMonoidal
open MonoidalCategory
open scoped TensorProduct

/-- The even element carried by a pair of odd vectors. -/
def oddPair {V W : SuperVect} (v : V.odd) (w : W.odd) :
    (SuperVect.tensorObj V W).even := (0, v ⊗ₜ[ℂ] w)

/-- Tensors of morphisms act blockwise on odd pairs. -/
theorem tensorHom_oddPair {V₁ V₂ W₁ W₂ : SuperVect}
    (g : V₁ ⟶ V₂) (h : W₁ ⟶ W₂) (v : V₁.odd) (w : W₁.odd) :
    ((g ⊗ₘ h : SuperVect.tensorObj V₁ W₁ ⟶
        SuperVect.tensorObj V₂ W₂) :
      SuperVect.Hom _ _).evenMap (oddPair v w) =
      oddPair ((g : SuperVect.Hom _ _).oddMap v)
        ((h : SuperVect.Hom _ _).oddMap w) := by
  change (SuperVect.tensorHom g h).evenMap (oddPair v w) = _
  change ((TensorProduct.map (g : SuperVect.Hom _ _).evenMap
        (h : SuperVect.Hom _ _).evenMap) 0,
    (TensorProduct.map (g : SuperVect.Hom _ _).oddMap
        (h : SuperVect.Hom _ _).oddMap) (v ⊗ₜ[ℂ] w)) = _
  rw [TensorProduct.map_tmul, map_zero]
  rfl

/-- The target unitor kills odd pairs of unit vectors. -/
theorem lambda_oddPair
    (v : SuperVect.tensorUnit.odd)
    (w : SuperVect.tensorUnit.odd) :
    (((λ_ (𝟙_ SuperVect)).hom :
        SuperVect.tensorObj SuperVect.tensorUnit
          SuperVect.tensorUnit ⟶ SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap (oddPair v w) = 0 := by
  change (TensorProduct.lid ℂ ℂ).toLinearMap
    ((LinearMap.fst ℂ _ _) (oddPair v w)) = 0
  rw [show (LinearMap.fst ℂ _ _) (oddPair v w) =
    (0 : ℂ ⊗[ℂ] ℂ) from rfl]
  rw [map_zero]

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))

-- The vanishing is checked through the tensorator
-- on the odd block, unfolding both unitors.
/-- **Split functionals vanish on odd pairs**: the tensor of two
copoint functionals kills a structure-map image of an odd
pair. -/
theorem omegaFun_tensor_oddPair {a b : ℕ}
    (q₁ : (SkeinObj.mk a : SkeinObj f) ⟶ SkeinObj.mk 0)
    (q₂ : (SkeinObj.mk b : SkeinObj f) ⟶ SkeinObj.mk 0)
    (v : (P.ω.obj (SkeinObj.mk a)).odd)
    (w : (P.ω.obj (SkeinObj.mk b)).odd) :
    letI := P.braided
    omegaFun f P (q₁ ⊗ₘ q₂)
        (((μ P.ω (SkeinObj.mk a) (SkeinObj.mk b)) :
          SuperVect.Hom _ _).evenMap (oddPair v w)) = 0 := by
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
      (z : SuperVect.Hom _ _).evenMap (oddPair v w)) habs
  refine Eq.trans ?_ (Eq.trans hev ?_)
  · rfl
  · change ((((P.ω.map q₁ ≫ η P.ω) ⊗ₘ (P.ω.map q₂ ≫ η P.ω)) ≫
        (λ_ (𝟙_ SuperVect)).hom :
        P.ω.obj (SkeinObj.mk a) ⊗ P.ω.obj (SkeinObj.mk b) ⟶
          SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap (oddPair v w) = 0
    change (((λ_ (𝟙_ SuperVect)).hom :
        SuperVect.tensorObj SuperVect.tensorUnit
          SuperVect.tensorUnit ⟶ SuperVect.tensorUnit) :
      SuperVect.Hom _ _).evenMap
      ((SuperVect.tensorHom
        (P.ω.map q₁ ≫ η P.ω) (P.ω.map q₂ ≫ η P.ω)).evenMap
        (oddPair v w)) = 0
    rw [show (SuperVect.tensorHom
        (P.ω.map q₁ ≫ η P.ω)
        (P.ω.map q₂ ≫ η P.ω)).evenMap (oddPair v w) =
      oddPair
        (((P.ω.map q₁ ≫ η P.ω : P.ω.obj (SkeinObj.mk a) ⟶
          SuperVect.tensorUnit) :
          SuperVect.Hom _ _).oddMap v)
        (((P.ω.map q₂ ≫ η P.ω : P.ω.obj (SkeinObj.mk b) ⟶
          SuperVect.tensorUnit) :
          SuperVect.Hom _ _).oddMap w) from
      tensorHom_oddPair _ _ v w]
    exact lambda_oddPair _ _

end RS
