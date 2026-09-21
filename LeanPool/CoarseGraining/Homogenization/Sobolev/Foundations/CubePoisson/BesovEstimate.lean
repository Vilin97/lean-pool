/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.GlobalComparison
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.Solver

/-! # Besov Estimate -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

/-!
# Calderon-Zygmund Besov gradient estimate for the cube Poisson solver

The narrow Calderon-Zygmund consequence used by the projected vector Poincare
proof: the gradient of the Neumann Poisson solution has controlled positive
`B¹_{2,∞}` circ norm, component by component, with the constant produced from
the coercive `H¹` bound and a geometric Besov scale weight.
-/

/-- The narrow Calderon-Zygmund consequence needed for the projected vector
Poincare proof: the gradient of the Neumann Poisson solution has controlled
positive `B¹_{2,∞}` circ norm, component by component. -/
def CubeNeumannPoissonGradientBesovEstimate {d : ℕ} (Q : TriadicCube d) (C : ℝ) :
    Prop :=
  0 ≤ C ∧
    ∀ (F : Vec d → ℝ)
      (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
      (_hmean : cubeAverage Q F = 0)
      (W : MeanZeroNeumannPoissonSolution Q F),
      ∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => W.w.toH1Function.grad x i) ≤
        C * cubeLpNorm Q (2 : ℝ≥0∞) F

/-- Componentwise geometric control of the positive `B¹_{2,∞}` circ norm by
normalized component `L²` norms. This is the Besov side of the narrow
Calderon-Zygmund dependency; the remaining elliptic part is to control the
Poisson-gradient component `L²` sum by the right-hand side. -/
theorem sum_cubeBesovCircNorm_one_two_top_le_geometric_mul_sum_cubeLpNorm
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → Vec d)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∑ i : Fin d,
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
          (fun x => G x i) ≤
      (cubeBesovScaleWeight (-1) Q * (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹) *
        ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i) := by
  let K : ℝ := cubeBesovScaleWeight (-1) Q * (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹
  have hcomponent :
      ∀ i : Fin d,
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => G x i) ≤
          K * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i) := by
    intro i
    have h :=
      cubeBesovCircNorm_le_geometric_constant_of_memLp
        (Q := Q) (s := 1) (p := (2 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞))
        (u := fun x => G x i) (by norm_num) (hG i)
        (by norm_num) (by norm_num) (by simp)
    calc
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞) (fun x => G x i)
          ≤ (cubeBesovScaleWeight (-1) Q *
              cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i)) *
              (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹ := h
      _ = K * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i) := by
            dsimp [K]
            ring
  calc
    ∑ i : Fin d,
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
          (fun x => G x i)
        ≤ ∑ i : Fin d, K * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i) := by
            exact Finset.sum_le_sum fun i _hi => hcomponent i
    _ = K * ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i) := by
          exact (Finset.mul_sum (s := Finset.univ)
            (f := fun i : Fin d => cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i)) K).symm
    _ = (cubeBesovScaleWeight (-1) Q * (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹) *
        ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞) (fun x => G x i) := by
          rfl

noncomputable def cubeNeumannPoissonGradientBesovEnergyConstant {d : ℕ}
    (Q : TriadicCube d) : ℝ :=
  (cubeBesovScaleWeight (-1) Q * (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹) *
    (((cubeVolume Q)⁻¹ + 1) * (d : ℝ) *
      cubeMeanZeroH1CoerciveConstant Q * (cubeVolume Q + 1))

theorem cubeNeumannPoissonGradientBesovEnergyConstant_nonneg {d : ℕ}
    (Q : TriadicCube d) :
    0 ≤ cubeNeumannPoissonGradientBesovEnergyConstant Q := by
  have hgeom : 0 ≤ cubeBesovScaleWeight (-1) Q *
      (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹ := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-1) Q) (by positivity)
  have hA : 0 ≤ (cubeVolume Q)⁻¹ + 1 := by
    have hInv : 0 ≤ (cubeVolume Q)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg Q)
    linarith
  have hB : 0 ≤ cubeVolume Q + 1 := by
    linarith [cubeVolume_nonneg Q]
  have henergy :
      0 ≤ ((cubeVolume Q)⁻¹ + 1) * (d : ℝ) *
        cubeMeanZeroH1CoerciveConstant Q * (cubeVolume Q + 1) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hA (Nat.cast_nonneg d))
        (cubeMeanZeroH1CoerciveConstant_nonneg Q))
      hB
  exact mul_nonneg hgeom henergy

theorem cubeNeumannPoissonGradientBesovEstimate_of_energy {d : ℕ}
    (Q : TriadicCube d) :
    CubeNeumannPoissonGradientBesovEstimate Q
      (cubeNeumannPoissonGradientBesovEnergyConstant Q) := by
  refine ⟨cubeNeumannPoissonGradientBesovEnergyConstant_nonneg Q, ?_⟩
  intro F hF _hmean W
  let K : ℝ := cubeBesovScaleWeight (-1) Q * (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹
  let E : ℝ :=
    ((cubeVolume Q)⁻¹ + 1) * (d : ℝ) *
      cubeMeanZeroH1CoerciveConstant Q * (cubeVolume Q + 1)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-1) Q) (by positivity)
  have hcirc :
      ∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => W.w.toH1Function.grad x i) ≤
        K * ∑ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) := by
    simpa [K] using
      sum_cubeBesovCircNorm_one_two_top_le_geometric_mul_sum_cubeLpNorm
        Q (fun x => W.w.toH1Function.grad x)
        (fun i => W.w.toH1Function.grad_memL2_normalizedCubeMeasure i)
  have henergy :
      ∑ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) ≤
        E * cubeLpNorm Q (2 : ℝ≥0∞) F := by
    simpa [E] using meanZeroNeumannPoissonSolution_sum_cubeLpNorm_grad_le Q hF W
  calc
    ∑ i : Fin d,
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
          (fun x => W.w.toH1Function.grad x i)
        ≤ K * ∑ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) := hcirc
    _ ≤ K * (E * cubeLpNorm Q (2 : ℝ≥0∞) F) := by
          exact mul_le_mul_of_nonneg_left henergy hK_nonneg
    _ = cubeNeumannPoissonGradientBesovEnergyConstant Q *
        cubeLpNorm Q (2 : ℝ≥0∞) F := by
          dsimp [K, E, cubeNeumannPoissonGradientBesovEnergyConstant]
          ring

end Homogenization
