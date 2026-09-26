/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CubeVectorH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp

/-!
# Coefficient rescaling for centered-cube divergence solutions

This file converts the normalized weak formulation with a positive scalar
coefficient into the raw cube Dirichlet divergence problem with rescaled data.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Dividing the positive scalar coefficient in the normalized centered-cube
weak formulation gives the raw cube divergence problem with inversely scaled
datum. -/
theorem centeredCubeH10ScalarDivergenceSolution_to_cubeDirichletDivergenceProblem
    {d : ℕ} (m : ℤ) (sigma0 : ℝ) {s : FractionalOrder}
    {p : FiniteLpExponent}
    (h : CubeEuclideanWspL2Field (originCube d m) s p)
    (w : H10Function (openCubeSet (originCube d m)))
    (hsigma0 : 0 < sigma0)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 w h.toLpTwo) :
    CubeDirichletDivergenceProblem (originCube d m) w
      (fun x => sigma0⁻¹ • h.toField x) := by
  intro phi
  have hmeasure : (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
    simp only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hsol := hsolution phi
  change sigma0 * ∫ x, vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume =
    -∫ x, vecDot (h.toField x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume at hsol
  rw [hmeasure, integral_smul_measure, integral_smul_measure,
    smul_eq_mul, smul_eq_mul] at hsol
  change ∫ x, vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)
      ∂(volume.restrict (openCubeSet (originCube d m))) =
    -∫ x, vecDot (sigma0⁻¹ • h.toField x) (phi.toH1Function.grad x)
      ∂(volume.restrict (openCubeSet (originCube d m)))
  simp only [vecDot_smul_left]
  change ∫ x, vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)
      ∂(volume.restrict (openCubeSet (originCube d m))) =
    -(∫ x, sigma0⁻¹ • vecDot (h.toField x) (phi.toH1Function.grad x)
      ∂(volume.restrict (openCubeSet (originCube d m))))
  rw [integral_smul]
  have hvol : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  have hcoeff :
      ENNReal.toReal (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) : ℝ≥0∞) =
        (cubeVolume (originCube d m))⁻¹ := by
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hvol.le)]
  rw [hcoeff] at hsol
  field_simp [hvol.ne'] at hsol
  calc
    ∫ x, vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)
        ∂(volume.restrict (openCubeSet (originCube d m))) =
        sigma0⁻¹ * (sigma0 * ∫ x,
          vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)
          ∂(volume.restrict (openCubeSet (originCube d m)))) := by
          field_simp [hsigma0.ne']
    _ = sigma0⁻¹ * (-(∫ x, vecDot (h.toField x) (phi.toH1Function.grad x)
          ∂(volume.restrict (openCubeSet (originCube d m))))) := by rw [hsol]
    _ = -(sigma0⁻¹ * (∫ x, vecDot (h.toField x) (phi.toH1Function.grad x)
          ∂(volume.restrict (openCubeSet (originCube d m))))) := by ring

end

end Homogenization
