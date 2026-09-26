/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.WeakHessianEuclidean
public import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedDomainCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.NormalizedLp

/-! # Euclidean Normalized -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-- The proof-carrying normalized `L²` norm of the internally centered
forcing.  This is the manuscript's `‖F - (F)_Q‖_{\underline{L}²(Q)}`. -/
noncomputable def centeredCubeNormalizedL2 {d : ℕ} (Q : TriadicCube d)
  (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) : ℝ :=
  (cubeBoundedMeasurableDomain Q).normalizedLpNorm (2 : ℝ≥0∞)
    (cubeFluctuation Q F)
    (by
      simpa [cubeFluctuation,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using!
        hF.sub (MeasureTheory.memLp_const (cubeAverage Q F)))

/-- A stronger regularity-producing centered-cube `q = 2` Neumann result.

This compatibility predicate concludes the existence of a weak Hessian.  The
source-facing predicate below instead estimates a weak-Hessian witness already
supplied by the caller. -/
def OriginCubeNeumannW22CalderonZygmundRegularityQTwo {d : ℕ} (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (m : ℤ) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m))),
    ∀ W : MeanZeroNeumannPoissonSolution (originCube d m)
        (cubeFluctuation (originCube d m) F),
      ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) W.w.toH1Function,
        H.frobeniusNormalizedL2 (originCube d m) ≤
          C * centeredCubeNormalizedL2 (originCube d m) F hF

/-- The dimension-only constant furnished by the reflected-parent Neumann
construction after normalized-volume scaling. -/
noncomputable def originCubeNeumannW22CalderonZygmundConstant (d : ℕ) : ℝ :=
  ((d : ℝ) * (d : ℝ)) *
    MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d 0

theorem originCubeNeumannW22CalderonZygmundConstant_nonneg (d : ℕ) :
    0 ≤ originCubeNeumannW22CalderonZygmundConstant d := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d))
    (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact_nonneg d 0)

theorem OriginCubeNeumannW22CalderonZygmundRegularityQTwo.constant_nonneg
    {d : ℕ} {C : ℝ} (h : OriginCubeNeumannW22CalderonZygmundRegularityQTwo (d := d) C) :
    0 ≤ C :=
  h.1

/-- Eliminate the regularity-producing Neumann predicate at a particular
scale, forcing, and supplied mean-zero solution. -/
theorem OriginCubeNeumannW22CalderonZygmundRegularityQTwo.apply
    {d : ℕ} {C : ℝ} (h : OriginCubeNeumannW22CalderonZygmundRegularityQTwo (d := d) C)
    (m : ℤ) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (W : MeanZeroNeumannPoissonSolution (originCube d m)
      (cubeFluctuation (originCube d m) F)) :
    ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) W.w.toH1Function,
      H.frobeniusNormalizedL2 (originCube d m) ≤
        C * centeredCubeNormalizedL2 (originCube d m) F hF :=
  h.2 m F hF W

theorem cubeAverage_centered_eq_zero {d : ℕ} (Q : TriadicCube d)
    {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => F x - cubeAverage Q F) = 0 := by
  rw [cubeAverage_sub_const_of_memLp_two Q hF]
  ring

theorem memLp_centered_normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d)
    {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp (fun x => F x - cubeAverage Q F) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  exact hF.sub (MeasureTheory.memLp_const (cubeAverage Q F))

theorem centeredCubeNormalizedL2_eq_cubeLpNorm {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    centeredCubeNormalizedL2 Q F hF =
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q F) := by
  change
    (MeasureTheory.eLpNorm (cubeFluctuation Q F) (2 : ℝ≥0∞)
      (cubeBoundedMeasurableDomain Q).normalizedVolume).toReal =
      (MeasureTheory.eLpNorm (cubeFluctuation Q F) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q)).toReal
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]

/-- The existing reflected-parent construction gives a regularity-producing
normalized-Frobenius estimate with a constant independent of cube scale. -/
theorem originCubeNeumannW22CalderonZygmund_regularity_qTwo :
    ∀ d : ℕ, OriginCubeNeumannW22CalderonZygmundRegularityQTwo (d := d)
      (originCubeNeumannW22CalderonZygmundConstant d) := by
  intro d
  refine ⟨originCubeNeumannW22CalderonZygmundConstant_nonneg d, ?_⟩
  intro m F hF W
  let Q : TriadicCube d := originCube d m
  let G : Vec d → ℝ := cubeFluctuation Q F
  have hG : MeasureTheory.MemLp G (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [G, cubeFluctuation] using! memLp_centered_normalizedCubeMeasure Q hF
  have hGmean : cubeAverage Q G = 0 := by
    exact cubeAverage_centered_eq_zero Q hF
  rcases
    W.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBoundExact
      hGmean hG with
    ⟨_uP, _huP_toFun, _huP_grad, H, hH⟩
  refine ⟨H, ?_⟩
  have hsum :
      (∑ i : Fin d, ∑ _j : Fin d,
        MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyBoundExact d m G i) ≤
        ((d : ℝ) * (d : ℝ)) *
          (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m *
            cubeLpNorm Q (2 : ℝ≥0∞) G) := by
    calc
      (∑ i : Fin d, ∑ _j : Fin d,
          MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyBoundExact d m G i)
          = ((d : ℝ) * (d : ℝ)) *
              (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m *
                cubeLpNorm Q (2 : ℝ≥0∞) G) := by
              simp [Q, G,
                MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyBoundExact_eq_constant_mul_cubeLpNorm]
              ring
      _ ≤ ((d : ℝ) * (d : ℝ)) *
              (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m *
                cubeLpNorm Q (2 : ℝ≥0∞) G) := le_rfl
  have hscale :
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum ≤
        ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          (((d : ℝ) * (d : ℝ)) *
            (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m *
              cubeLpNorm Q (2 : ℝ≥0∞) G)) := by
    refine mul_le_mul_of_nonneg_left (hH.trans hsum) ?_
    exact Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _
  have hcancel :=
    MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact_volume_cancel d m
  calc
    H.frobeniusNormalizedL2 Q
        ≤ ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum :=
          H.frobeniusNormalizedL2_le_volumeNormalized_hessianCoordL2NormSum Q
    _ ≤ ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          (((d : ℝ) * (d : ℝ)) *
            (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m *
              cubeLpNorm Q (2 : ℝ≥0∞) G)) := hscale
    _ = originCubeNeumannW22CalderonZygmundConstant d *
          centeredCubeNormalizedL2 Q F hF := by
          rw [centeredCubeNormalizedL2_eq_cubeLpNorm]
          simp only [originCubeNeumannW22CalderonZygmundConstant]
          change
            ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                ((d : ℝ) * (d : ℝ) *
                  (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m *
                    cubeLpNorm Q (2 : ℝ≥0∞) G)) =
              ((d : ℝ) * (d : ℝ)) *
                MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d 0 *
                  cubeLpNorm Q (2 : ℝ≥0∞) G
          calc
            ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                ((d : ℝ) * (d : ℝ) *
                  (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m *
                    cubeLpNorm Q (2 : ℝ≥0∞) G)) =
                ((d : ℝ) * (d : ℝ)) *
                  ((((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                    MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m) *
                      cubeLpNorm Q (2 : ℝ≥0∞) G) := by ring
            _ = ((d : ℝ) * (d : ℝ)) *
                  (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d 0 *
                    cubeLpNorm Q (2 : ℝ≥0∞) G) := by
                  rw [show
                    ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                        MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m =
                      MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d 0 by
                        simpa [Q] using hcancel]
            _ = ((d : ℝ) * (d : ℝ)) *
                MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d 0 *
                  cubeLpNorm Q (2 : ℝ≥0∞) G := by ring

/-- Apply the regularity-producing `q = 2` centered-cube Neumann result. -/
theorem originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply
    (d : ℕ) (m : ℤ) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (W : MeanZeroNeumannPoissonSolution (originCube d m)
      (cubeFluctuation (originCube d m) F)) :
    ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) W.w.toH1Function,
      H.frobeniusNormalizedL2 (originCube d m) ≤
        originCubeNeumannW22CalderonZygmundConstant d *
          centeredCubeNormalizedL2 (originCube d m) F hF :=
  OriginCubeNeumannW22CalderonZygmundRegularityQTwo.apply
    (originCubeNeumannW22CalderonZygmund_regularity_qTwo d) m F hF W

/-- The literal centered-cube `q = 2` Neumann Calderón--Zygmund branch from
the source.  The caller supplies arbitrary `F`; the mean-zero right-hand side
is formed internally as `F - (F)_{\cu_m}`, and the estimate applies to every
supplied mean-zero solution and every supplied weak-Hessian witness. -/
def OriginCubeNeumannW22CalderonZygmundQTwo {d : ℕ} (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (m : ℤ) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m))),
    ∀ (W : MeanZeroNeumannPoissonSolution (originCube d m)
        (cubeFluctuation (originCube d m) F))
      (H : HasWeakHessianOn (openCubeSet (originCube d m)) W.w.toH1Function),
      H.frobeniusNormalizedL2 (originCube d m) ≤
        C * centeredCubeNormalizedL2 (originCube d m) F hF

theorem OriginCubeNeumannW22CalderonZygmundQTwo.constant_nonneg
    {d : ℕ} {C : ℝ} (h : OriginCubeNeumannW22CalderonZygmundQTwo (d := d) C) :
    0 ≤ C :=
  h.1

/-- Apply the literal Neumann branch to a supplied mean-zero solution and
weak-Hessian witness. -/
theorem OriginCubeNeumannW22CalderonZygmundQTwo.apply
    {d : ℕ} {C : ℝ} (h : OriginCubeNeumannW22CalderonZygmundQTwo (d := d) C)
    (m : ℤ) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (W : MeanZeroNeumannPoissonSolution (originCube d m)
      (cubeFluctuation (originCube d m) F))
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) W.w.toH1Function) :
    H.frobeniusNormalizedL2 (originCube d m) ≤
      C * centeredCubeNormalizedL2 (originCube d m) F hF :=
  h.2 m F hF W H

/-- The explicit normalized-Frobenius constant proves the literal
source-facing Neumann branch.  A regularity-producing witness is constructed
internally, then weak-derivative uniqueness transfers its estimate to every
supplied witness. -/
theorem originCubeNeumannW22CalderonZygmund_qTwo :
    ∀ d : ℕ, OriginCubeNeumannW22CalderonZygmundQTwo (d := d)
      (originCubeNeumannW22CalderonZygmundConstant d) := by
  intro d
  refine ⟨originCubeNeumannW22CalderonZygmundConstant_nonneg d, ?_⟩
  intro m F hF W H
  rcases originCubeNeumannW22CalderonZygmund_regularity_qTwo_apply d m F hF W with
    ⟨K, hK⟩
  rw [H.frobeniusNormalizedL2_eq_of_hasWeakHessianOn (originCube d m) K]
  exact hK

end

end Homogenization
