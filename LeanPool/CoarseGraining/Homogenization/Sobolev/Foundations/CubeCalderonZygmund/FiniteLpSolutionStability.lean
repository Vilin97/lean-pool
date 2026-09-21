/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpBelowTwo

/-!
# Stability of finite-exponent cube divergence solutions

The supplied-solution cube Calderón--Zygmund estimate applies to the
difference of two zero-trace solutions.  This file packages that subtraction
step, retaining the same exponent-only constant and the exact inverse
coefficient scaling.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private noncomputable def cubeEuclideanL2LpFieldSub
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h k : CubeEuclideanL2LpField Q q) : CubeEuclideanL2LpField Q q where
  toField := fun x => h.toField x - k.toField x
  euclideanMemLp := by
    exact h.euclideanMemLp.sub k.euclideanMemLp
  euclideanMemL2 := by
    exact h.euclideanMemL2.sub k.euclideanMemL2

@[simp] private theorem cubeEuclideanL2LpFieldSub_toField
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h k : CubeEuclideanL2LpField Q q) :
    (cubeEuclideanL2LpFieldSub h k).toField = fun x => h.toField x - k.toField x :=
  rfl

private theorem H10Function.sub_grad
    {d : ℕ} {U : Set (Vec d)} (u v : H10Function U) :
    (u - v).toH1Function.grad = fun x => u.toH1Function.grad x - v.toH1Function.grad x := by
  change (u.toH1Function - v.toH1Function).grad = _
  rw [H1Function.sub_grad]

private theorem memVectorL2_openCubeSet_of_euclideanMemLpTwo
    {d : ℕ} (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q)) :
    MemVectorL2 (openCubeSet Q) F := by
  have hvec : MemLp F 2 (normalizedCubeMeasure Q) := by
    apply MemLp.of_eval
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF.eval_piLp i
  have hle :
      cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [Measure.smul_apply, Measure.smul_apply]
      change ENNReal.ofReal (cubeVolume Q) *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) * cubeMeasure Q s) = cubeMeasure Q s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hcube : MemLp F 2 (cubeMeasure Q) :=
    hvec.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
      ENNReal.ofReal_ne_top hle
  simpa only [MemVectorL2, volumeMeasureOn, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hcube

private theorem centeredCube_integrable_vecDot_of_memVectorL2
    {d : ℕ} (m : ℤ) {F G : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet (originCube d m)) F)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    Integrable (fun x => vecDot (F x) (G x))
      (centeredCubeDomain d m).normalizedVolume := by
  rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
    change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
  exact (integrableOn_vecDot_of_memVectorL2 hF hG).smul_measure ENNReal.ofReal_ne_top

private theorem isCenteredCubeH10ScalarDivergenceSolution_sub
    {d : ℕ} {q : FiniteLpExponent} (m : ℤ) (sigma0 : ℝ)
    (h k : CubeEuclideanL2LpField (originCube d m) q)
    (u v : H10Function (openCubeSet (originCube d m)))
    (hu : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo)
    (hv : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 v k.toLpTwo) :
    IsCenteredCubeH10ScalarDivergenceSolution m sigma0 (u - v)
      (cubeEuclideanL2LpFieldSub h k).toLpTwo := by
  intro phi
  have hu_phi := hu phi
  have hv_phi := hv phi
  change sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume =
    -∫ x, vecDot (h.toField x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume at hu_phi
  change sigma0 * ∫ x, vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume =
    -∫ x, vecDot (k.toField x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume at hv_phi
  change sigma0 * ∫ x, vecDot ((u.toH1Function - v.toH1Function).grad x)
      (phi.toH1Function.grad x) ∂(centeredCubeDomain d m).normalizedVolume =
    -∫ x, vecDot (h.toField x - k.toField x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume
  rw [H1Function.sub_grad]
  simp_rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hhu := centeredCube_integrable_vecDot_of_memVectorL2 m
    u.toH1Function.grad_memVectorL2 phi.toH1Function.grad_memVectorL2
  have hhv := centeredCube_integrable_vecDot_of_memVectorL2 m
    v.toH1Function.grad_memVectorL2 phi.toH1Function.grad_memVectorL2
  have hhh := centeredCube_integrable_vecDot_of_memVectorL2 m
    (memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m) h.euclideanMemL2)
    phi.toH1Function.grad_memVectorL2
  have hhk := centeredCube_integrable_vecDot_of_memVectorL2 m
    (memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m) k.euclideanMemL2)
    phi.toH1Function.grad_memVectorL2
  change sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x) -
      vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume =
    -∫ x, vecDot (h.toField x) (phi.toH1Function.grad x) -
      vecDot (k.toField x) (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume
  rw [integral_sub hhu hhv, integral_sub hhh hhk, mul_sub]
  linarith

namespace INTERNAL

/-- Two zero-trace scalar divergence solutions on the same centered cube are
Lipschitz in their data in the normalized Euclidean `L^q` gradient norm.  The
constant is precisely the one supplied by
`centeredCubeH10ScalarDivergence_cz`. -/
theorem centeredCubeH10ScalarDivergence_solution_stability
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h k : CubeEuclideanL2LpField (originCube d m) q)
      (u v : H10Function (openCubeSet (originCube d m))), 0 < sigma0 →
      IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo →
      IsCenteredCubeH10ScalarDivergenceSolution m sigma0 v k.toLpTwo →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
          (fun x => u.toH1Function.grad x - v.toH1Function.grad x) ≤
        C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            (fun x => h.toField x - k.toField x) := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_cz d q
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h k u v hsigma0 hu hv
  have hsub := hC m sigma0 (cubeEuclideanL2LpFieldSub h k) (u - v) hsigma0
    (isCenteredCubeH10ScalarDivergenceSolution_sub m sigma0 h k u v hu hv)
  simpa only [H10Function.sub_grad, cubeEuclideanL2LpFieldSub_toField] using hsub

end INTERNAL

end CubeCalderonZygmund

end
end Homogenization
