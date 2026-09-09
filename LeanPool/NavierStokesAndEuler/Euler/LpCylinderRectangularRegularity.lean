/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductAt
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Same-radius mixed cylinder bounds for the physical frame and forcing

The translated coefficient is lifted through actual norm-one maps. Only
its coefficient radius pays the finite alphabet and fixed Sobolev order.
The input field's external-word radius is preserved by the true product
estimate, using bounds only at the base translation.
-/

@[expose] public section


noncomputable section

namespace EulerLpCylinderRectangular

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerMeanCoefficients
  EulerGevrey EulerParameterWordGevrey
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {E F K ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace K] [CompactSpace K] [Fintype ι]

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRectangularRegularity1 : NormedAddCommGroup (E →L[ℝ] F) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRectangularRegularity2 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity3 : NormedAddCommGroup (Space →ᵇ E →L[ℝ] F) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity4 : NormedSpace ℝ (Space →ᵇ E →L[ℝ] F) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ E →L[ℝ] F)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRectangularRegularity5 : NormedAddCommGroup C(K,Space →ᵇ E →L[ℝ] F) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity6 : NormedSpace ℝ C(K,Space →ᵇ E →L[ℝ] F) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 period E)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity7 : NormedAddCommGroup (CylinderL2 period E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 period E)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity8 : NormedSpace ℝ (CylinderL2 period E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 period F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity9 : NormedAddCommGroup (CylinderL2 period F) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 period F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity10 : NormedSpace ℝ (CylinderL2 period F) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,CylinderL2 period E)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRectangularRegularity11 : NormedAddCommGroup C(K,CylinderL2 period E)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,CylinderL2 period E)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity12 : NormedSpace ℝ C(K,CylinderL2 period E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,CylinderL2 period F)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRectangularRegularity13 : NormedAddCommGroup C(K,CylinderL2 period F)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,CylinderL2 period F)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRectangularRegularity14 : NormedSpace ℝ C(K,CylinderL2 period F) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period
F))` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRectangularRegularity15 : NormedAddCommGroup (C(K,CylinderL2 period E)
    →L[ℝ] C(K,CylinderL2 period
    F)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period F))`
instance to shorten typeclass synthesis. -/
local instance instLpCylinderRectangularRegularity16 : NormedSpace ℝ (C(K,CylinderL2 period E)
    →L[ℝ] C(K,CylinderL2 period F)) :=
    inferInstance

variable (A : C(K, Space →ᵇ E →L[ℝ] F)) (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

/-- The actual rectangular multiplier family under all four covering translations. -/
def mixedMultiplier (a : LiftTangent) : C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period F) :=
  fullMultiplierMap period (translateCoefficientPath A a.1)

include hA in
theorem mixedMultiplier_contDiff : ContDiff ℝ ∞ (mixedMultiplier period A) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,Space →ᵇ E →L[ℝ] F))
    (F := C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period F))
    (fullMultiplierMap period)).comp (hA.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff)

include hA in
/-- The genuine mixed multiplier jets have exactly the bounded-field coefficient bound. -/
theorem mixedMultiplier_bound (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (mixedMultiplier period A) a‖ ≤ C := by
  let f := translateCoefficientPath A
  have hright : ‖iteratedFDeriv ℝ n (f ∘ ContinuousLinearMap.fst ℝ Space ℝ) a‖ ≤ C := by
    rw [(ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right hA a (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    calc
      _ ≤ ‖iteratedFDeriv ℝ n f a.1‖ * ∏ _i : Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
      _ ≤ C := by simpa only [Finset.prod_const_one,mul_one] using hb a.1
  have hleft := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
    (F := C(K,Space →ᵇ E →L[ℝ] F))
    (G := C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period F))
    (fullMultiplierMap period)
    ((hA.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).contDiffAt (x := a)) (n := n) (by simp)
  exact hleft.trans ((mul_le_mul_of_nonneg_right (fullMultiplierMap_norm period)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hright))

include hA in
/-- Applying the physical frame or projected-forcing coefficient preserves actual mixed smoothness.
-/
theorem product_orbit_contDiff (u : C(K, CylinderL2 period E))
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a u)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (fullMultiplierMap period A u)) :=
        by
  have he : (fun a : LiftTangent => pathTranslate period a (fullMultiplierMap period A u)) =
      (fun a => mixedMultiplier period A a (pathTranslate period a u)) :=
    funext (fun a => (fullMultiplier_translation period a A u).symm)
  rw [he]
  exact (mixedMultiplier_contDiff period A hA).clm_apply hu

include hA in
/-- True fixed-Hq mixed word bounds for actual coefficient application. The
field radius R is identical on both sides. -/
theorem product_orbit_block_bound (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q
    : ℕ)
    (u : C(K, CylinderL2 period E))
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a u))
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbA : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) a‖ ≤ C*majorant Rc 0 n)
    (d : ℕ) (hbu : ∀ n, block directions q (fun a : LiftTangent => pathTranslate period a u) n 0 ≤
      D*majorant R d n) (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate period a (fullMultiplierMap period A
        u)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C*D)*majorant R d n := by
  have he : (fun a : LiftTangent => pathTranslate period a (fullMultiplierMap period A u)) =
      (fun a => mixedMultiplier period A a (pathTranslate period a u)) :=
    funext (fun a => (fullMultiplier_translation period a A u).symm)
  rw [he]
  exact block_clm_apply_gevrey_at directions q (mixedMultiplier period A)
    (fun a : LiftTangent => pathTranslate period a u) (mixedMultiplier_contDiff period A hA) hu 0
    (sobolevCoefficientRadius ι Rc) R (sobolevCoefficientAmplitude ι q Rc C) D
    (sobolevCoefficientRadius_nonneg Rc hRc) hR (sobolevCoefficientAmplitude_nonneg q Rc C hRc hC)
        hD
    (fun j => coefficientBlock_of_tensor_bound directions hd q (mixedMultiplier period A)
      (mixedMultiplier_contDiff period A hA) Rc C hRc hC
      (fun k a => mixedMultiplier_bound period A hA k (C*majorant Rc 0 k) (hbA k) a) j 0)
    d hbu n

include hA in
theorem supported_product_orbit_contDiff (S : Set Space) (hS : MeasurableSet S)
    (u : C(K, Supported period E S hS))
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS u)))
        :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (supportedMultiplierMap period S hS A u))) := by
  rw [include_supportedMultiplier]
  exact product_orbit_contDiff period A hA (includePath period S hS u) hu

end EulerLpCylinderRectangular
