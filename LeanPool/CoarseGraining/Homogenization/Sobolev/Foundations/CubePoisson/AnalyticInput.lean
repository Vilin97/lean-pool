/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.EndpointDuality

/-! # Analytic Input -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal Topology

/-!
# Analytic-input bundles, integral helpers, and `H1Function` Poisson surface

This file packages the analytic-input bundles used by the cube-local vector
Poincare proofs (full, full-`L²`, and projected), the `cubeAverage` ↔
`integralAverage` and `setIntegral` ↔ `cubeBesovPairing` identities, and the
`H1Function`-side Poisson right-hand side and mean-zero representative.
-/

/-- Corrected analytic input bundle for the full-dual vector Poincare theorem.
It keeps the same Poisson solver and Neumann CZ field as the legacy bundle, but
uses the full endpoint-duality surface that retains constant modes. -/
structure CubeFullVectorPoincareAnalyticInput {d : ℕ} (Q : TriadicCube d) where
  poisson : HasMeanZeroNeumannPoissonSolverOnCube Q
  czConstant : ℝ
  cz : CubeNeumannPoissonGradientBesovEstimate Q czConstant
  dualityConstant : ℝ
  duality : CubePoissonGradientFullEndpointDuality Q dualityConstant

/-- Slim corrected analytic input bundle for the full-dual vector Poincare
theorem after the Poisson-gradient endpoint estimate has already been combined
with the Neumann CZ estimate. This is the interface downstream arguments should
aim to use: a solver plus one direct `L²` endpoint constant. -/
structure CubeFullVectorPoincareL2AnalyticInput {d : ℕ} (Q : TriadicCube d) where
  poisson : HasMeanZeroNeumannPoissonSolverOnCube Q
  endpointConstant : ℝ
  endpoint : CubePoissonGradientFullL2EndpointDuality Q endpointConstant

namespace CubeFullVectorPoincareL2AnalyticInput

variable {d : ℕ} {Q : TriadicCube d}

theorem endpointConstant_nonneg (h : CubeFullVectorPoincareL2AnalyticInput Q) :
    0 ≤ h.endpointConstant :=
  h.endpoint.1

end CubeFullVectorPoincareL2AnalyticInput

namespace CubeFullVectorPoincareAnalyticInput

variable {d : ℕ} {Q : TriadicCube d}

theorem czConstant_nonneg (h : CubeFullVectorPoincareAnalyticInput Q) :
    0 ≤ h.czConstant :=
  h.cz.1

theorem dualityConstant_nonneg (h : CubeFullVectorPoincareAnalyticInput Q) :
    0 ≤ h.dualityConstant :=
  h.duality.1

/-- Collapse the split corrected full endpoint plus Neumann CZ bundle into the
direct `L²` endpoint bundle. -/
noncomputable def to_l2AnalyticInput (h : CubeFullVectorPoincareAnalyticInput Q) :
    CubeFullVectorPoincareL2AnalyticInput Q where
  poisson := h.poisson
  endpointConstant := h.dualityConstant * h.czConstant
  endpoint := h.duality.to_l2Endpoint h.cz

end CubeFullVectorPoincareAnalyticInput

/-- A bundled interface for the classical analytic ingredients behind the
single-cube projected vector Poincare theorem. -/
structure CubeProjectedVectorPoincareAnalyticInput {d : ℕ} (Q : TriadicCube d) where
  poisson : HasMeanZeroNeumannPoissonSolverOnCube Q
  czConstant : ℝ
  cz : CubeNeumannPoissonGradientBesovEstimate Q czConstant
  dualityConstant : ℝ
  duality : CubeProjectedGradientEndpointDuality Q dualityConstant
  fullDualityConstant : ℝ
  fullDuality : CubeGradientEndpointDuality Q fullDualityConstant

namespace CubeProjectedVectorPoincareAnalyticInput

variable {d : ℕ} {Q : TriadicCube d}

theorem czConstant_nonneg (h : CubeProjectedVectorPoincareAnalyticInput Q) :
    0 ≤ h.czConstant :=
  h.cz.1

theorem dualityConstant_nonneg (h : CubeProjectedVectorPoincareAnalyticInput Q) :
    0 ≤ h.dualityConstant :=
  h.duality.1

theorem fullDualityConstant_nonneg (h : CubeProjectedVectorPoincareAnalyticInput Q) :
    0 ≤ h.fullDualityConstant :=
  h.fullDuality.1

end CubeProjectedVectorPoincareAnalyticInput

theorem cubeAverage_eq_integralAverage_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q f = integralAverage (openCubeSet Q) f := by
  unfold cubeAverage integralAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet, volume_openCubeSet_toReal]

theorem setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume =
      cubeVolume Q * cubeAverage Q f := by
  have hQ : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  have havg := cubeAverage_eq_integralAverage_openCubeSet Q f
  calc
    ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume
        = cubeVolume Q *
            ((cubeVolume Q)⁻¹ *
              ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume) := by
            field_simp [hQ]
    _ = cubeVolume Q * cubeAverage Q f := by
          rw [havg]
          simp [integralAverage, volume_openCubeSet_toReal]

theorem setIntegral_openCubeSet_mul_eq_cubeVolume_mul_cubeBesovPairing {d : ℕ}
    (Q : TriadicCube d) (f g : Vec d → ℝ) :
    ∫ x in openCubeSet Q, f x * g x ∂MeasureTheory.volume =
      cubeVolume Q * cubeBesovPairing Q f g := by
  simp [cubeBesovPairing, setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage]

/-- The unnormalized square integral on the open cube is the cube volume times
the square of the normalized `L²` norm. -/
theorem setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in openCubeSet Q, f x * f x ∂MeasureTheory.volume =
      cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℝ) := by
  have hnorm := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
    (Q := Q) (p := (2 : ℝ≥0∞)) (f := f) (by norm_num) (by simp) hf
  have hnorm2 :
      (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℝ) =
        cubeAverage Q (fun x => ‖f x‖ ^ (2 : ℝ)) := by
    simpa using hnorm
  have hnorm' :
      (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℝ) =
        cubeAverage Q (fun x => f x * f x) := by
    rw [hnorm2]
    apply cubeAverage_congr_on_cubeSet
    intro x _hx
    simp [Real.norm_eq_abs, pow_two]
  rw [setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage]
  rw [← hnorm']

namespace H1Function

variable {d : ℕ} {Q : TriadicCube d}

/-- The mean-zero right-hand side for the cube Neumann Poisson problem
associated to an `H¹` function. -/
noncomputable def cubePoissonRhs (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) : Vec d → ℝ :=
  cubeFluctuation Q (fun x => u x)

@[simp] theorem cubePoissonRhs_apply (u : H1Function (openCubeSet Q)) (x : Vec d) :
    u.cubePoissonRhs Q x = u x - cubeAverage Q (fun x => u x) :=
  rfl

theorem cubePoissonRhs_memL2_normalizedCubeMeasure
    (u : H1Function (openCubeSet Q)) :
    MeasureTheory.MemLp (u.cubePoissonRhs Q) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hu : MeasureTheory.MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverage Q (fun x => u x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const
      (μ := normalizedCubeMeasure Q) (p := (2 : ℝ≥0∞)) (cubeAverage Q (fun x => u x))
  simpa [H1Function.cubePoissonRhs, cubeFluctuation] using! hu.sub hconst

theorem cubeAverage_cubePoissonRhs (u : H1Function (openCubeSet Q)) :
    cubeAverage Q (u.cubePoissonRhs Q) = 0 := by
  simp [H1Function.cubePoissonRhs]

@[simp] theorem cubeBesovOscillation_eq_cubeLpNorm_cubePoissonRhs
    (u : H1Function (openCubeSet Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u x) =
      cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) :=
  rfl

/-- The open-cube mean-zero representative of an `H¹` function, with the
normalization chosen to match `cubePoissonRhs`. -/
noncomputable def toMeanZeroOnCube (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    H1MeanZeroFunction (openCubeSet Q) := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact u.toMeanZero

@[simp] theorem toMeanZeroOnCube_apply
    (u : H1Function (openCubeSet Q)) (x : Vec d) :
    u.toMeanZeroOnCube Q x = u.cubePoissonRhs Q x := by
  unfold H1Function.toMeanZeroOnCube
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have havg :
      integralAverage (openCubeSet Q) (fun x => u x) =
        cubeAverage Q (fun x => u x) :=
    (cubeAverage_eq_integralAverage_openCubeSet Q (fun x => u x)).symm
  simp [H1Function.cubePoissonRhs, havg]

@[simp] theorem toMeanZeroOnCube_grad
    (u : H1Function (openCubeSet Q)) (x : Vec d) :
    (u.toMeanZeroOnCube Q).toH1Function.grad x = u.grad x := by
  unfold H1Function.toMeanZeroOnCube
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  simp

theorem grad_coord_memL2_normalizedCubeMeasure
    (u : H1Function (openCubeSet Q)) (i : Fin d) :
    MeasureTheory.MemLp (fun x => u.grad x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
  u.grad_memL2_normalizedCubeMeasure i

theorem grad_coord_memL2_normalizedCubeMeasure_descendant
    {R : TriadicCube d} {j : ℕ}
    (u : H1Function (openCubeSet Q)) (hR : R ∈ descendantsAtDepth Q j) (i : Fin d) :
    MeasureTheory.MemLp (fun x => u.grad x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
  u.grad_memL2_normalizedCubeMeasure_of_mem_descendantsAtDepth hR i

end H1Function

end Homogenization
