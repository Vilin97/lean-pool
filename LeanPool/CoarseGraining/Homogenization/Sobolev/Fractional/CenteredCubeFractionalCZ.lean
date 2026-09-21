/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeFractionalGradientMemLp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspLpMembership
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePFullCZ

/-!
# Fractional Calderón--Zygmund estimate on centered cubes

This module packages the supplied zero-trace cube solution with the literal
Euclidean fractional-Sobolev field carried by its gradient.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A supplied zero-trace centered-cube divergence solution with fractional
`L² ∩ L^q` datum has a literal fractional-Sobolev gradient, with a constant
uniform in the cube scale, coefficient scale, and fractional order. -/
theorem centeredCubeH10ScalarDivergence_fractional_cz
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (sigma0 : ℝ) (s : FractionalOrder)
        (h : CubeEuclideanWspL2Field (originCube d m) s q)
        (w : H10Function (openCubeSet (originCube d m))),
        0 < sigma0 →
        IsCenteredCubeH10ScalarDivergenceSolution m sigma0 w h.toLpTwo →
          ∃ gradW : CubeEuclideanWspField (originCube d m) s q,
            gradW.toField = w.toH1Function.grad ∧
              cubeEuclideanWspESeminorm
                  (originCube d m) s q gradW.toField ≤
                C * (ENNReal.ofReal sigma0)⁻¹ *
                  cubeEuclideanWspESeminorm
                    (originCube d m) s q h.toField := by
  obtain ⟨Cfull, hCfull_top, hfull⟩ := exists_exactOverlapFiniteP_full_cz d q
  let K : ℝ≥0∞ := cubeEuclideanWspOverlapDimensionConstant d
  let C : ℝ≥0∞ := K * Cfull * K
  have hK_top : K < ∞ := by
    simpa only [K] using cubeEuclideanWspOverlapDimensionConstant_lt_top d
  refine ⟨C, ENNReal.mul_lt_top (ENNReal.mul_lt_top hK_top hCfull_top) hK_top, ?_⟩
  intro m sigma0 s h w hsigma0 hsolution
  let Q : TriadicCube d := originCube d m
  have hgradLp := centeredCubeH10ScalarDivergence_grad_memLp d q m sigma0 s h w
    hsigma0 hsolution
  let gradLp : CubeEuclideanLpField Q q :=
    { toField := w.toH1Function.grad
      euclideanMemLp := by simpa only [Q] using hgradLp }
  have hOverlapGrad :
      cubeEuclideanPositiveBesovOverlapESeminorm Q s q w.toH1Function.grad ≤
        Cfull * (ENNReal.ofReal sigma0)⁻¹ *
          cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField := by
    simpa only [Q] using hfull m sigma0 s h w hsigma0 hsolution
  have hOverlapData :
      cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField ≤
        K * cubeEuclideanWspESeminorm Q s q h.toField := by
    simpa only [Q, K] using
      cubeEuclideanOverlap_le_dimensionConstant_mul_wsp Q s q h.toCubeEuclideanLpField
  have hWspGrad :
      cubeEuclideanWspESeminorm Q s q w.toH1Function.grad ≤
        K * cubeEuclideanPositiveBesovOverlapESeminorm Q s q w.toH1Function.grad := by
    simpa only [Q, K] using
      cubeEuclideanWsp_le_dimensionConstant_mul_overlap Q s q gradLp
  have hDataWsp_top : cubeEuclideanWspESeminorm Q s q h.toField < ∞ := by
    simpa only [Q] using h.euclideanMemWsp.eSeminorm_lt_top
  have hOverlapData_top :
      cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField < ∞ :=
    lt_of_le_of_lt hOverlapData (ENNReal.mul_lt_top hK_top hDataWsp_top)
  have hSigma_top : (ENNReal.ofReal sigma0)⁻¹ < ∞ :=
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0))).lt_top
  have hOverlapGrad_top :
      cubeEuclideanPositiveBesovOverlapESeminorm Q s q w.toH1Function.grad < ∞ :=
    lt_of_le_of_lt hOverlapGrad
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hCfull_top hSigma_top) hOverlapData_top)
  have hWspGrad_top : cubeEuclideanWspESeminorm Q s q w.toH1Function.grad < ∞ :=
    lt_of_le_of_lt hWspGrad (ENNReal.mul_lt_top hK_top hOverlapGrad_top)
  let gradW : CubeEuclideanWspField Q s q :=
    { toField := w.toH1Function.grad
      euclideanMemLp := gradLp.euclideanMemLp
      euclideanMemWsp :=
        memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top gradLp.euclideanMemLp hWspGrad_top }
  refine ⟨gradW, rfl, ?_⟩
  calc
    cubeEuclideanWspESeminorm (originCube d m) s q gradW.toField =
        cubeEuclideanWspESeminorm Q s q w.toH1Function.grad := by rfl
    _ ≤ K * cubeEuclideanPositiveBesovOverlapESeminorm Q s q w.toH1Function.grad :=
      hWspGrad
    _ ≤ K * (Cfull * (ENNReal.ofReal sigma0)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField) := by
          gcongr
    _ ≤ K * (Cfull * (ENNReal.ofReal sigma0)⁻¹ *
        (K * cubeEuclideanWspESeminorm Q s q h.toField)) := by
          gcongr
    _ = C * (ENNReal.ofReal sigma0)⁻¹ *
        cubeEuclideanWspESeminorm (originCube d m) s q h.toField := by
          simp only [C, Q]
          ring

end

end Homogenization
