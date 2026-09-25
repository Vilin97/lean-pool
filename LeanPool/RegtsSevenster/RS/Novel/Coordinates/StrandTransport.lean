/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EvFormOdd

/-!
# The one-strand transport collapse

The transport at one strand is the left-unitor composite of the
strand identification: the counit-tensor coherence with the
strict skein unitor eliminated.  Its even and odd evaluations on
unit-padded vectors are the strand identification itself.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped TensorProduct

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

/-- **The one-strand transport is the unitor composite.** -/
theorem stdToOmega_one :
    letI := P.braided
    stdToOmega f P e 1 =
      (SuperVect.tensorUnit ◁ e) ≫
        (λ_ (P.ω.obj (SkeinObj.mk 1))).hom := by
  let := P.braided
  change (stdToOmega f P e 0 ⊗ₘ e) ≫
    μ P.ω (SkeinObj.mk 0) (SkeinObj.mk 1) = _
  have h := Functor.LaxMonoidal.ε_tensorHom_comp_μ
    (F := P.ω) (X := SkeinObj.mk 1) e
  rw [show (λ_ (SkeinObj.mk 1 : SkeinObj f)).inv =
      𝟙 (SkeinObj.mk 1) from by
    change bundleMapClass f (finCongr _) = _
    rw [show (finCongr (show (1 : ℕ) = 0 + 1 by omega) :
        Fin 1 ≃ Fin 1) = _root_.Equiv.refl (Fin 1) from
      _root_.Equiv.ext (fun x => Fin.ext rfl)]
    exact bundleMapClass_refl f 1] at h
  rw [show P.ω.map (𝟙 (SkeinObj.mk 1 : SkeinObj f)) =
      𝟙 (P.ω.obj (SkeinObj.mk 1)) from P.ω.map_id _] at h
  rw [Category.comp_id] at h
  exact h

-- Raised budget: the one-strand transport is unfolded through the
-- tensorator and the left unitor.
/-- The even evaluation of the one-strand transport on a
unit-padded even vector. -/
theorem stdToOmega_one_even (x : (stdSuperPair k ℓ).even) :
    letI := P.braided
    ((stdToOmega f P e 1) : SuperVect.Hom _ _).evenMap
        (evenPair (1 : ℂ) x) =
      (e : SuperVect.Hom _ _).evenMap x := by
  let := P.braided
  rw [stdToOmega_one]
  change (((λ_ (P.ω.obj (SkeinObj.mk 1))).hom :
      SuperVect.tensorObj SuperVect.tensorUnit
        (P.ω.obj (SkeinObj.mk 1)) ⟶
      P.ω.obj (SkeinObj.mk 1)) : SuperVect.Hom _ _).evenMap
      ((SuperVect.tensorHom (SuperVect.Hom.id _) e).evenMap
        (evenPair (1 : ℂ) x)) = _
  rw [show (SuperVect.tensorHom
      (SuperVect.Hom.id (𝟙_ SuperVect)) e).evenMap
      (evenPair (1 : ℂ) x) =
    evenPair (1 : ℂ) ((e : SuperVect.Hom _ _).evenMap x) from by
    change ((TensorProduct.map LinearMap.id
        (e : SuperVect.Hom _ _).evenMap) ((1 : ℂ) ⊗ₜ[ℂ] x),
      (TensorProduct.map
        (SuperVect.Hom.id (𝟙_ SuperVect)).oddMap
        (e : SuperVect.Hom _ _).oddMap) 0) = _
    rw [TensorProduct.map_tmul, map_zero]
    rfl]
  exact (TensorProduct.lid_tmul _ _).trans (one_smul _ _)

/-- The unit-padded odd element. -/
def oddUnitPad {V : SuperVect} (y : V.odd) :
    (SuperVect.tensorObj SuperVect.tensorUnit V).odd :=
  ((1 : ℂ) ⊗ₜ[ℂ] y, 0)

-- As for the even component, on the odd half.
/-- The odd evaluation of the one-strand transport on a
unit-padded odd vector. -/
theorem stdToOmega_one_odd (y : (stdSuperPair k ℓ).odd) :
    letI := P.braided
    ((stdToOmega f P e 1) : SuperVect.Hom _ _).oddMap
        (oddUnitPad y) =
      (e : SuperVect.Hom _ _).oddMap y := by
  let := P.braided
  rw [stdToOmega_one]
  change (((λ_ (P.ω.obj (SkeinObj.mk 1))).hom :
      SuperVect.tensorObj SuperVect.tensorUnit
        (P.ω.obj (SkeinObj.mk 1)) ⟶
      P.ω.obj (SkeinObj.mk 1)) : SuperVect.Hom _ _).oddMap
      ((SuperVect.tensorHom (SuperVect.Hom.id _) e).oddMap
        (oddUnitPad y)) = _
  rw [show (SuperVect.tensorHom
      (SuperVect.Hom.id (𝟙_ SuperVect)) e).oddMap
      (oddUnitPad y) =
    oddUnitPad ((e : SuperVect.Hom _ _).oddMap y) from by
    change ((TensorProduct.map LinearMap.id
        (e : SuperVect.Hom _ _).oddMap) ((1 : ℂ) ⊗ₜ[ℂ] y),
      (TensorProduct.map
        (SuperVect.Hom.id (𝟙_ SuperVect)).oddMap
        (e : SuperVect.Hom _ _).evenMap) 0) = _
    rw [TensorProduct.map_tmul, map_zero]
    rfl]
  exact (TensorProduct.lid_tmul _ _).trans (one_smul _ _)

end RS
