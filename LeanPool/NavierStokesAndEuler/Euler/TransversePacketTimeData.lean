/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
public import LeanPool.NavierStokesAndEuler.Euler.DeformationTimeInverse
public import LeanPool.NavierStokesAndEuler.Euler.SourcePotentialTimePath

@[expose] public section

/-! Time identities derived from the source deformation data, including the actual inverse and
  normal paths. -/

noncomputable section

namespace EulerTransversePacketProvider.Data

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseBoundedFrame EulerBoundedFieldCalculus EulerOperatorGevreyCalculus
  EulerGevrey EulerSourcePotentialCoefficient EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space) :=
  inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space) :=
  inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space) := inferInstance

/-- The derivative of the inverse is constructed from the original fields. -/
def inverseDerivative : C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space) :=
  -pathCompositionMap D.FInv.field D.M.field

/-- The derivative of the transported normal is the fixed adjoint-vector map of that path. -/
def normalDerivative : C(Icc (0 : ℝ) D.T,Space →ᵇ Space) :=
  mapCoefficientPath (normalMap D.m₀) D.inverseDerivative

@[simp] theorem inverseDerivative_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.inverseDerivative t x = -((D.FInv.field t x).comp (D.M.field t x)) := rfl

@[simp] theorem normalDerivative_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.normalDerivative t x = -((D.M.field t x).adjoint (D.normal.field t x)) := by
  change (-((D.FInv.field t x).comp (D.M.field t x))).adjoint D.m₀ =
    -((D.M.field t x).adjoint ((D.FInv.field t x).adjoint D.m₀))
  simp only [map_neg, adjoint_comp, neg_apply, comp_apply]

/-- No differentiability of F⁻¹ is assumed: it follows from the actual inverse identities and F_t=MF. -/
theorem inverse_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.FInv.field r x)
      (extendPath D.T D.T_pos.le D.inverseDerivative t x) (Icc (0 : ℝ) D.T) t := by
  have hFG (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) D.T) :
      (extendPath D.T D.T_pos.le D.F.field r x).comp
        (extendPath D.T D.T_pos.le D.FInv.field r x) = ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.inverse_right (projIcc 0 D.T D.T_pos.le r) x v
  have hGF (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) D.T) :
      (extendPath D.T D.T_pos.le D.FInv.field r x).comp
        (extendPath D.T D.T_pos.le D.F.field r x) = ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.inverse_left (projIcc 0 D.T D.T_pos.le r) x v
  have hF₁ : extendPath D.T D.T_pos.le D.F₁.field t x =
      (extendPath D.T D.T_pos.le D.M.field t x).comp
        (extendPath D.T D.T_pos.le D.F.field t x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.strain_equation (projIcc 0 D.T D.T_pos.le t) x v
  have hF := D.frame_time t ht x
  rw [hF₁] at hF
  exact EulerDeformationTime.inverse_strain_hasDerivWithinAt (Icc (0 : ℝ) D.T) t ht
    (fun r => extendPath D.T D.T_pos.le D.F.field r x)
    (fun r => extendPath D.T D.T_pos.le D.FInv.field r x)
    (extendPath D.T D.T_pos.le D.M.field t x) hFG hGF hF

theorem normal_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.normal.field r x)
      (extendPath D.T D.T_pos.le D.normalDerivative t x) (Icc (0 : ℝ) D.T) t := by
  exact (normalMap D.m₀).hasFDerivAt.comp_hasDerivWithinAt t
    (D.inverse_hasDerivWithinAt t ht x)

theorem inverseDerivative_translation :
    translateCoefficientPath D.inverseDerivative = fun a =>
      -pathCompositionMap (translateCoefficientPath D.FInv.field a)
        (translateCoefficientPath D.M.field a) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem normalDerivative_translation :
    translateCoefficientPath D.normalDerivative = fun a =>
      mapCoefficientPath (normalMap D.m₀) (translateCoefficientPath D.inverseDerivative a) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem inverseDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.inverseDerivative) := by
  rw [D.inverseDerivative_translation]
  exact (pathComposition_contDiff _ _ D.FInv.translation_contDiff D.M.translation_contDiff).neg

theorem normalDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.normalDerivative) := by
  rw [D.normalDerivative_translation]
  exact (mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀)).contDiff.comp
    D.inverseDerivative_orbit

theorem normalPathMap_norm :
    ‖mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).mpr
  intro x
  change ‖normalMap D.m₀ (A t x)‖ ≤ ‖A‖
  calc
    _ ≤ ‖normalMap D.m₀‖ * ‖A t x‖ := (normalMap D.m₀).le_opNorm _
    _ ≤ 1 * ‖A t x‖ := mul_le_mul_of_nonneg_right (normalMap_norm D.m₀ D.m₀_unit) (norm_nonneg _)
    _ ≤ ‖A‖ := by simpa only [one_mul] using ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)

theorem inverseDerivative_bound (R CI CM : ℝ) (hR : 0 ≤ R) (hCI : 0 ≤ CI) (hCM : 0 ≤ CM)
    (hI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ CI*majorant R 0 n)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.M.field) a‖ ≤ CM*majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤ (3*CI*CM)*majorant R 0
      n := by
  rw [D.inverseDerivative_translation]
  exact neg_bound _ R (3*CI*CM) 0
    (pathComposition_bound _ _ D.FInv.translation_contDiff D.M.translation_contDiff
      R CI CM hR hCI hCM 0 0 hI hM) n a

theorem normalDerivative_bound (R CI CM : ℝ) (hR : 0 ≤ R) (hCI : 0 ≤ CI) (hCM : 0 ≤ CM)
    (hI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ CI*majorant R 0 n)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.M.field) a‖ ≤ CM*majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.normalDerivative) a‖ ≤ (3*CI*CM)*majorant R 0 n
      := by
  rw [D.normalDerivative_translation]
  exact contraction_bound (mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀))
    D.normalPathMap_norm _ D.inverseDerivative_orbit R (3*CI*CM) hR (by positivity) 0
    (D.inverseDerivative_bound R CI CM hR hCI hCM hI hM) n a

/-- The actual time coefficient for the periodic-potential multiplier. -/
def potentialDerivative : C(Icc (0 : ℝ) D.T,PotentialField) :=
  potentialTimePath D.normal D.normalDerivative D.normalLower D.normalLower_pos D.normal_lower

theorem potentialDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.potentialDerivative) :=
  potentialTimePath_orbit D.normal D.normalDerivative D.normalLower D.normalLower_pos D.normal_lower
    D.normalDerivative_orbit

theorem potential_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le
      (potentialCoefficient D.normal D.normalLower D.normalLower_pos D.normal_lower) r x)
      (D.potentialDerivative t x) (Icc (0 : ℝ) D.T) t := by
  convert potentialTimePath_hasDerivWithinAt D.T D.T_pos.le D.normal D.normalDerivative
    D.normalLower D.normalLower_pos D.normal_lower D.normal_hasDerivWithinAt t x using 1
  dsimp only [potentialDerivative]

end EulerTransversePacketProvider.Data
