/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderNormalBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive

@[expose] public section

/-!
# Source coefficient bounds for the actual pressure path

The normal inverse is constructed from m, and the angular primitive is the
actual bounded scalar cylinder operator. The resulting fixed-Hq estimate
uses one fixed external radius and adds no shift to its supplied inputs.
-/

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
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖^2)
  (f v : C(K,CylinderL2 P Space))

def sourceResidual : C(K,CylinderL2 P ℝ) :=
  normalResidualPath P (normalFunctional m cm hcm hm) M.field f v

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
  3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*Cm)*
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
