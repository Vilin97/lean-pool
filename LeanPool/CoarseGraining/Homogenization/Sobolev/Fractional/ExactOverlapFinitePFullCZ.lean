/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeDivergenceRescaling
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePHomogeneity
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePOneDepthCZ

/-!
# Global finite-`p` exact-overlap Calderón--Zygmund estimate

The one-depth exact-overlap estimate is summed with the source scale weights,
then rooted at the finite exponent.  The coefficient scale is removed by
rescaling the datum before applying the one-depth result.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem enorm_inv_eq_ofReal_inv {sigma : ℝ} (hsigma : 0 < sigma) :
    ‖sigma⁻¹‖ₑ = (ENNReal.ofReal sigma)⁻¹ := by
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hsigma.le),
    ENNReal.ofReal_inv_of_pos hsigma]

/-- The global exact-overlap finite-`p` Calderón--Zygmund estimate for a
supplied centered-cube divergence solution.  Its constant is fixed before
the cube scale, fractional order, coefficient scale, datum, and solution. -/
theorem exists_exactOverlapFiniteP_full_cz
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (sigma0 : ℝ) (s : FractionalOrder)
        (h : CubeEuclideanWspL2Field (originCube d m) s q)
        (w : H10Function (openCubeSet (originCube d m))),
        0 < sigma0 →
        IsCenteredCubeH10ScalarDivergenceSolution m sigma0 w h.toLpTwo →
        cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s q
          w.toH1Function.grad ≤
          C * (ENNReal.ofReal sigma0)⁻¹ *
            cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s q
              h.toField := by
  obtain ⟨C, hCtop, hdepth⟩ := exists_exactOverlapFiniteP_oneDepth_cz d q
  let r : ℝ := q.exponent.toReal
  have hr_pos : 0 < r :=
    ENNReal.toReal_pos (zero_lt_one.trans q.one_lt).ne' q.lt_top.ne
  have hr_nonneg : 0 ≤ r := hr_pos.le
  refine ⟨C ^ r⁻¹,
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hCtop.ne, ?_⟩
  intro m sigma0 s h w hsigma0 hsolution
  let Q : TriadicCube d := originCube d m
  let hscaled : Vec d → Vec d := fun x => sigma0⁻¹ • h.toField x
  have hscaled_l2 : MemLp (fun x => HilbertVec.ofVec (hscaled x)) 2
      (normalizedCubeMeasure Q) := by
    simpa only [hscaled, ← (HilbertVec.ofVecL d).map_smul] using!
      h.euclideanMemL2.const_smul sigma0⁻¹
  have hscaled_q : MemLp (fun x => HilbertVec.ofVec (hscaled x)) q.exponent
      (normalizedCubeMeasure Q) := by
    simpa only [hscaled, ← (HilbertVec.ofVecL d).map_smul] using!
      h.euclideanMemLp.const_smul sigma0⁻¹
  have hproblem : CubeDirichletDivergenceProblem Q w hscaled := by
    simpa only [Q, hscaled] using
      centeredCubeH10ScalarDivergenceSolution_to_cubeDirichletDivergenceProblem
        m sigma0 h w hsigma0 hsolution
  have hdepth_scaled : ∀ j : ℕ,
      (cubeEuclideanPositiveBesovOverlapDepthENorm Q q w.toH1Function.grad j) ^ r ≤
        C * ‖sigma0⁻¹‖ₑ ^ r *
          (cubeEuclideanPositiveBesovOverlapDepthENorm Q q h.toField j) ^ r := by
    intro j
    have hlocal := hdepth m j hscaled hscaled_l2 hscaled_q w hproblem
    have hhom := cubeEuclideanPositiveBesovOverlapDepthENorm_const_smul_rpow
      Q q h.toField sigma0⁻¹ h.euclideanMemLp j
    calc
      (cubeEuclideanPositiveBesovOverlapDepthENorm Q q w.toH1Function.grad j) ^ r ≤
          C * (cubeEuclideanPositiveBesovOverlapDepthENorm Q q hscaled j) ^ r := by
            simpa only [Q, hscaled, r] using hlocal
      _ = C * ‖sigma0⁻¹‖ₑ ^ r *
          (cubeEuclideanPositiveBesovOverlapDepthENorm Q q h.toField j) ^ r := by
            rw [hhom]
            ring
  have hpower :
      (cubeEuclideanPositiveBesovOverlapESeminorm Q s q w.toH1Function.grad) ^ r ≤
        C * ‖sigma0⁻¹‖ₑ ^ r *
          (cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField) ^ r := by
    let weight : ℕ → ℝ≥0∞ := fun j =>
      ENNReal.ofReal (Real.rpow 3
        (-(s.1 * q.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ) : ℝ)))))
    rw [cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy,
      cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy,
      cubeEuclideanPositiveBesovOverlapPowerEnergy_eq_tsum_depthENorm,
      cubeEuclideanPositiveBesovOverlapPowerEnergy_eq_tsum_depthENorm]
    change (∑' j : ℕ, weight j *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q q w.toH1Function.grad j) ^ r) ≤
      C * ‖sigma0⁻¹‖ₑ ^ r * ∑' j : ℕ, weight j *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q q h.toField j) ^ r
    calc
      (∑' j : ℕ, weight j *
          (cubeEuclideanPositiveBesovOverlapDepthENorm Q q w.toH1Function.grad j) ^ r) ≤
          ∑' j : ℕ, C * ‖sigma0⁻¹‖ₑ ^ r *
            (weight j *
              (cubeEuclideanPositiveBesovOverlapDepthENorm Q q h.toField j) ^ r) := by
            apply ENNReal.tsum_le_tsum
            intro j
            calc
              weight j *
                  (cubeEuclideanPositiveBesovOverlapDepthENorm Q q w.toH1Function.grad j) ^ r ≤
                  weight j * (C * ‖sigma0⁻¹‖ₑ ^ r *
                    (cubeEuclideanPositiveBesovOverlapDepthENorm Q q h.toField j) ^ r) :=
                    mul_le_mul_right (hdepth_scaled j) _
              _ = C * ‖sigma0⁻¹‖ₑ ^ r *
                  (weight j *
                    (cubeEuclideanPositiveBesovOverlapDepthENorm Q q h.toField j) ^ r) := by
                    ring
      _ = C * ‖sigma0⁻¹‖ₑ ^ r *
          ∑' j : ℕ,
            weight j *
              (cubeEuclideanPositiveBesovOverlapDepthENorm Q q h.toField j) ^ r :=
            ENNReal.tsum_mul_left
  have hfactor :
      (C ^ r⁻¹ * (ENNReal.ofReal sigma0)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField) ^ r =
        C * ‖sigma0⁻¹‖ₑ ^ r *
          (cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField) ^ r := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr_nonneg,
      ENNReal.mul_rpow_of_nonneg _ _ hr_nonneg,
      ENNReal.rpow_inv_rpow hr_pos.ne', enorm_inv_eq_ofReal_inv hsigma0]
  have hroot := ENNReal.rpow_le_rpow hpower (show 0 ≤ r⁻¹ by positivity)
  calc
    cubeEuclideanPositiveBesovOverlapESeminorm Q s q w.toH1Function.grad =
        (cubeEuclideanPositiveBesovOverlapESeminorm Q s q w.toH1Function.grad ^ r) ^ r⁻¹ :=
          (ENNReal.rpow_rpow_inv hr_pos.ne' _).symm
    _ ≤ (C * ‖sigma0⁻¹‖ₑ ^ r *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField ^ r) ^ r⁻¹ := hroot
    _ = C ^ r⁻¹ * (ENNReal.ofReal sigma0)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s q h.toField := by
          rw [← hfactor, ENNReal.rpow_rpow_inv hr_pos.ne']

end

end Homogenization
