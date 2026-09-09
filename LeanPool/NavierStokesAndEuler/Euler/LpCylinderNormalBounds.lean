/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevOperations

@[expose] public section

/-! Actual normal pressure residuals preserve the fixed-Sobolev mixed-word radius. -/

noncomputable section

namespace EulerLpCylinderRectangular

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMeanCoefficients EulerParameterWordGevrey EulerGevrey
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {K E ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  (N : C(K,Space →ᵇ E →L[ℝ] ℝ)) (M : C(K,Space →ᵇ E →L[ℝ] E))
  (f v : C(K,CylinderL2 period E))

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
      (3*sobolevCoefficientAmplitude ι q Rc CN*(Df+6*sobolevCoefficientAmplitude ι q Rc CM*Dv))*
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
      ((add_le_add (hbf j) (hs.trans (mul_le_mul_of_nonneg_left (hwb j) (by norm_num)))).trans_eq
        (by ring))
  exact product_orbit_block_bound period N hN directions hd q (f - (2 : ℝ) • w) hres
    Rc CN R (Df+6*sobolevCoefficientAmplitude ι q Rc CM*Dv) hRc hCN
    (add_nonneg hDf (mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg q Rc CM hRc hCM)) hDv)) hR hbN d hresb n

end EulerLpCylinderRectangular
