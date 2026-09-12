/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevOperations
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Source coefficient bounds for the actual pressure path

The normal inverse is constructed from m, and the angular primitive is the
actual bounded scalar cylinder operator. The resulting fixed-Hq estimate
uses one fixed external radius and adds no shift to its supplied inputs.
-/

section

/-! Actual normal pressure residuals preserve the fixed-Sobolev mixed-word radius. -/

@[expose] public section

noncomputable section

namespace EulerLpCylinderRectangular

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMeanCoefficients EulerParameterWordGevrey EulerGevrey
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {K E ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  (N : C(K, Space →ᵇ E →L[ℝ] ℝ)) (M : C(K, Space →ᵇ E →L[ℝ] E))
  (f v : C(K, CylinderL2 period E))

/-- The actual scalar coefficient of the normal residual, as a cylinder L² path. -/
def normalResidualPath : C(K,CylinderL2 period ℝ) :=
  fullMultiplierMap period N (f - (2 : ℝ) • fullMultiplierMap period M v)

theorem normalResidualPath_contDiff
    (hN : ContDiff ℝ ∞ (translateCoefficientPath N))
    (hM : ContDiff ℝ ∞ (translateCoefficientPath M))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f))
    (hv : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a v)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (normalResidualPath period N M f
        v)) := by
  apply product_orbit_contDiff period N hN
  simpa only [map_sub,map_smul] using
    hf.sub ((product_orbit_contDiff period M hM v hv).const_smul (2 : ℝ))

/-- Both multiplications and the subtraction preserve exactly the input external radius. -/
theorem normalResidualPath_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hN : ContDiff ℝ ∞ (translateCoefficientPath N))
    (hM : ContDiff ℝ ∞ (translateCoefficientPath M))
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f))
    (hv : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a v))
    (Rc CN CM R Df Dv : ℝ) (hRc : 0 ≤ Rc) (hCN : 0 ≤ CN) (hCM : 0 ≤ CM)
    (hDf : 0 ≤ Df) (hDv : 0 ≤ Dv) (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath N) a‖ ≤ CN*majorant Rc 0 n)
    (hbM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath M) a‖ ≤ CM*majorant Rc 0 n)
    (d : ℕ)
    (hbf : ∀ n, block directions q (fun a : LiftTangent => pathTranslate period a f) n 0 ≤
        Df*majorant R d n)
    (hbv : ∀ n, block directions q (fun a : LiftTangent => pathTranslate period a v) n 0 ≤
        Dv*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate period a (normalResidualPath period N
        M f v)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc CN*(Df+6*sobolevCoefficientAmplitude ι q Rc CM*Dv)) *
        majorant R d n := by
  let w := fullMultiplierMap period M v
  have hw : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a w) :=
    product_orbit_contDiff period M hM v hv
  have hwb (j : ℕ) : block directions q (fun a : LiftTangent => pathTranslate period a w) j 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc CM*Dv)*majorant R d j :=
    product_orbit_block_bound period M hM directions hd q v hv Rc CM R Dv hRc hCM hDv hR hbM d hbv j
  have hres : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (f - (2 : ℝ) • w)) := by
    simpa only [map_sub,map_smul] using hf.sub (hw.const_smul (2 : ℝ))
  have hresb (j : ℕ) : block directions q (fun a : LiftTangent => pathTranslate period a (f - (2 :
      ℝ) • w)) j 0 ≤
      (Df+6*sobolevCoefficientAmplitude ι q Rc CM*Dv)*majorant R d j := by
    have he : (fun a : LiftTangent => pathTranslate period a (f - (2 : ℝ) • w)) =
        (fun a => pathTranslate period a f - (2 : ℝ) • pathTranslate period a w) := by
      funext a
      simp only [map_sub,map_smul]
    rw [he]
    have hs := block_smul_le directions q (2 : ℝ) (fun a : LiftTangent => pathTranslate period a w)
        hw j 0
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hs
    exact (block_sub_le directions q (fun a : LiftTangent => pathTranslate period a f)
      (fun a : LiftTangent => (2 : ℝ) • pathTranslate period a w) hf (hw.const_smul 2) j 0).trans
      ((add_le_add (hbf j) (hs.trans (mul_le_mul_of_nonneg_left (hwb j) (by
          norm_num)))).trans_eq (by ring))
  exact product_orbit_block_bound period N hN directions hd q (f - (2 : ℝ) • w) hres
    Rc CN R (Df+6*sobolevCoefficientAmplitude ι q Rc CM*Dv) hRc hCN
    (add_nonneg hDf (mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg q Rc CM hRc hCM)) hDv)) hR hbN d hresb n

end EulerLpCylinderRectangular

end
end

end

@[expose] public section

noncomputable section

namespace EulerSourceNormalResidualBounds

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerSourceNormalCoefficient
  EulerCylinderScalarPrimitive EulerParameterWordGevrey EulerGevrey EulerTimeLpGramGevrey
  EulerTransverseForwardCoefficientGevrey EulerOperatorGevreyCalculus
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K ι : Type*} [TopologicalSpace K] [CompactSpace K] [Fintype ι]
  (M : SmoothCoefficientPath K (Space →L[ℝ] Space)) (m : SmoothCoefficientPath K Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)
  (f v : C(K, CylinderL2 P Space))

/-- Source residual, given by `normalResidualPath P (normalFunctional m cm hcm hm) M.field f v`. -/
def sourceResidual : C(K,CylinderL2 P ℝ) :=
  normalResidualPath P (normalFunctional m cm hcm hm) M.field f v

/-- Source pressure, given by `pathPrimitive P (sourceResidual P M m cm hcm hm f v)`. -/
def sourcePressure : C(K,CylinderL2 P ℝ) :=
  pathPrimitive P (sourceResidual P M m cm hcm hm f v)

theorem sourceResidual_contDiff
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
    (hv : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a v)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (sourceResidual P M m cm hcm hm f v)) :=
  normalResidualPath_contDiff P (normalFunctional m cm hcm hm) M.field f v
    (normalFunctional_translation_contDiff m cm hcm hm) M.translation_contDiff hf hv

theorem sourcePressure_contDiff
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
    (hv : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a v)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (sourcePressure P M m cm hcm hm f v)) :=
  pathPrimitive_orbit_contDiff P _ (sourceResidual_contDiff P M m cm hcm hm f v hf hv)

/-- An explicit fixed-order coefficient polynomial for the pressure source. -/
def pressureCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri Cm CM Df Dv : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*Cm) *
    (Df+6*sobolevCoefficientAmplitude ι q (4*Ri) CM*Dv)

theorem sourceResidual_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
    (hv : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a v))
    (Rc Cm CM Ri R Df Dv : ℝ) (hRc : 0 ≤ Rc) (hCm : 0 ≤ Cm) (hCM : 0 ≤ CM)
    (hDf : 0 ≤ Df) (hDv : 0 ≤ Dv) (hRi : 2*gramCost cm Cm 1*(Rc+1) ≤ Ri)
    (hR : sobolevCoefficientRadius ι (4*Ri) ≤ R)
    (hbm : ∀ n t x, ‖iteratedFDeriv ℝ n (m.field t : Space → Space) x‖ ≤ Cm*majorant Rc 0 n)
    (hbM : ∀ n t x, ‖iteratedFDeriv ℝ n (M.field t : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc
        0 n)
    (d : ℕ)
    (hbf : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a f) n 0 ≤ Df*majorant R
        d n)
    (hbv : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a v) n 0 ≤ Dv*majorant R
        d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (sourceResidual P M m cm hcm hm f
        v)) n 0 ≤
      pressureCost ι q Ri Cm CM Df Dv*majorant R d n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds cm Cm Rc Ri hcm hRc hRi
  have hMr (j : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ j (translateCoefficientPath M.field) a‖ ≤ CM*majorant (4*Ri) 0 j :=
    (M.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hCM (majorant_nonneg Rc hRc 0 j)) (hbM j)
        a).trans
      (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hCM)
  exact normalResidualPath_block_bound P (normalFunctional m cm hcm hm) M.field f v directions hd q
    (normalFunctional_translation_contDiff m cm hcm hm) M.translation_contDiff hf hv
    (4*Ri) (3*Ri*Cm) CM R Df Dv (by positivity) (by positivity) hCM hDf hDv hR
    (normalFunctional_translation_bound m cm hcm hm Rc Cm Ri hRc hCm hRi hbm) hMr d hbf hbv n

/-- The actual normalized angular pressure costs only the period, and preserves
the supplied fixed-order block, external radius, and shift. -/
theorem sourcePressure_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
    (hv : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a v))
    (Rc Cm CM Ri R Df Dv : ℝ) (hRc : 0 ≤ Rc) (hCm : 0 ≤ Cm) (hCM : 0 ≤ CM)
    (hDf : 0 ≤ Df) (hDv : 0 ≤ Dv) (hRi : 2*gramCost cm Cm 1*(Rc+1) ≤ Ri)
    (hR : sobolevCoefficientRadius ι (4*Ri) ≤ R)
    (hbm : ∀ n t x, ‖iteratedFDeriv ℝ n (m.field t : Space → Space) x‖ ≤ Cm*majorant Rc 0 n)
    (hbM : ∀ n t x, ‖iteratedFDeriv ℝ n (M.field t : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc
        0 n)
    (d : ℕ)
    (hbf : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a f) n 0 ≤ Df*majorant R
        d n)
    (hbv : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a v) n 0 ≤ Dv*majorant R
        d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (sourcePressure P M m cm hcm hm f
        v)) n 0 ≤
      (P*pressureCost ι q Ri Cm CM Df Dv)*majorant R d n := by
  have hr := sourceResidual_block_bound P M m cm hcm hm f v directions hd q hf hv
    Rc Cm CM Ri R Df Dv hRc hCm hCM hDf hDv hRi hR hbm hbM d hbf hbv n
  have hp := pathPrimitive_block_le P directions q (sourceResidual P M m cm hcm hm f v)
    (sourceResidual_contDiff P M m cm hcm hm f v hf hv) n 0
  exact hp.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hr (le_of_lt (Fact.out : 0 < P)))

end EulerSourceNormalResidualBounds
