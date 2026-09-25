/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.MasterSum

/-!
# Star coordinate symmetry

The star vector is permutation-invariant, the inverse transport
intertwines permutations, and hence the star coordinate at a
permuted colouring is the odd-inversion sign times the original.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- **The star vector is permutation-invariant.** -/
theorem starVec_perm (d : ℕ) (σ : _root_.Equiv.Perm (Fin d)) :
    ((P.ω.map (bundleMapClass f (σ : Fin d ≃ Fin d))) :
      SuperVect.Hom _ _).evenMap (starVec f P d) =
      starVec f P d := by
  refine Eq.trans (omegaVec_comp f P _ _).symm ?_
  exact congrArg (omegaVec f P) (vertexStarClass_perm f d σ)

/-- **The inverse transport intertwines permutations.** -/
theorem stdFromOmega_perm
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    (d : ℕ) (σ : _root_.Equiv.Perm (Fin d)) :
    letI := P.braided
    (stdFromOmega f P e' d ≫ modelPermMap σ :
      P.ω.obj (SkeinObj.mk d) ⟶ superPow (stdSuperPair k ℓ) d) =
      P.ω.map (bundleMapClass f (σ : Fin d ≃ Fin d)) ≫
        stdFromOmega f P e' d := by
  let := P.braided
  have h1 : modelPermMap (k := k) (ℓ := ℓ) σ =
      stdToOmega f P e d ≫
        P.ω.map (bundleMapClass f (σ : Fin d ≃ Fin d)) ≫
        stdFromOmega f P e' d := by
    have h2 := congrArg (fun z :
        (superPow (stdSuperPair k ℓ) d ⟶
          P.ω.obj (SkeinObj.mk d)) =>
      z ≫ stdFromOmega f P e' d)
      (stdToOmega_bmc_perm_all f P e d σ)
    simp only [Category.assoc] at h2
    rw [stdToOmega_stdFromOmega f P e e' he'e d,
      Category.comp_id] at h2
    exact h2.symm
  rw [h1]
  rw [← Category.assoc]
  rw [stdFromOmega_stdToOmega f P e e' hee' d]
  rw [Category.id_comp]

-- Raised budget: `rfl`, but the two sides agree only after the
-- transport and the coordinate extraction are unfolded.
/-- The star coordinate is a model coordinate. -/
theorem starCoord_eq_coordOf (d : ℕ)
    (c : MixedColouring k ℓ d) :
    starCoord f P e' d c =
      coordOf (((stdFromOmega f P e' d) :
        SuperVect.Hom _ _).evenMap (starVec f P d)) c := rfl

-- Raised budget: the symmetry is read through the transport and
-- the colouring equivalence, so the permutation action unfolds on
-- both.
/-- **The star coordinate symmetry**: permuting the colouring
multiplies by the odd-inversion sign. -/
theorem starCoord_perm
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    (d : ℕ) (σ : _root_.Equiv.Perm (Fin d))
    (c : MixedColouring k ℓ d) :
    starCoord f P e' d (c ∘ σ) =
      (-1 : ℂ) ^ oddInversions σ c * starCoord f P e' d c := by
  let := P.braided
  have hfix : ((modelPermMap σ) : SuperVect.Hom _ _).evenMap
      (((stdFromOmega f P e' d) :
        SuperVect.Hom _ _).evenMap (starVec f P d)) =
      ((stdFromOmega f P e' d) :
        SuperVect.Hom _ _).evenMap (starVec f P d) := by
    have h := congrArg (fun z :
        (P.ω.obj (SkeinObj.mk d) ⟶
          superPow (stdSuperPair k ℓ) d) =>
      (z : SuperVect.Hom _ _).evenMap (starVec f P d))
      (stdFromOmega_perm f P e e' hee' he'e d σ)
    refine Eq.trans h ?_
    change ((stdFromOmega f P e' d) :
      SuperVect.Hom _ _).evenMap
      (((P.ω.map (bundleMapClass f
          (σ : Fin d ≃ Fin d))) :
        SuperVect.Hom _ _).evenMap (starVec f P d)) = _
    rw [starVec_perm f P d σ]
  have hcoord := coordOf_modelPermMap' σ
    (((stdFromOmega f P e' d) :
      SuperVect.Hom _ _).evenMap (starVec f P d)) c
  rw [hfix] at hcoord
  rw [starCoord_eq_coordOf, starCoord_eq_coordOf]
  rw [hcoord]
  rw [← mul_assoc]
  rw [show ((-1 : ℂ) ^ oddInversions σ c) *
      ((-1 : ℂ) ^ oddInversions σ c) = 1 from by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨oddInversions σ c, rfl⟩]
  rw [one_mul]

end RS
