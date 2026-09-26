/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.Regularity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.WeakHessianEuclidean
public import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedDomainCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.NormalizedLp

/-! # Euclidean Normalized -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

namespace CubeDirichletWeakPoissonProblem

/-- A stronger regularity-producing centered-cube `q = 2` Dirichlet result.

Unlike the manuscript statement, this compatibility predicate concludes the
existence of a weak Hessian.  The source-facing predicate below instead takes
a supplied weak-Hessian witness and estimates that witness. -/
def OriginCubeDirichletCalderonZygmundRegularityQTwo (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (m : ℤ) (u : H10Function (openCubeSet (originCube d m)))
    (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F),
    ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
      H.frobeniusNormalizedL2 (originCube d m) ≤
        C * (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
          (2 : ℝ≥0∞) F (by
            simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
              using hF)

theorem OriginCubeDirichletCalderonZygmundRegularityQTwo.constant_nonneg
    {d : ℕ} {C : ℝ} (h : OriginCubeDirichletCalderonZygmundRegularityQTwo d C) :
    0 ≤ C :=
  h.1

theorem OriginCubeDirichletCalderonZygmundRegularityQTwo.apply
    {d : ℕ} {C : ℝ} (h : OriginCubeDirichletCalderonZygmundRegularityQTwo d C)
    (m : ℤ) (u : H10Function (openCubeSet (originCube d m))) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F) :
    ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
      H.frobeniusNormalizedL2 (originCube d m) ≤
        C * (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
          (2 : ℝ≥0∞) F (by
            simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
              using hF) :=
  h.2 m u F hF hweak

/-- The regularity-producing centered-cube Dirichlet `q = 2` endpoint. -/
theorem exists_originCube_dirichlet_calderon_zygmund_regularity_q_two
    {d : ℕ} [NeZero d] (m : ℤ)
    (u : H10Function (openCubeSet (originCube d m))) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F) :
    ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
      H.frobeniusNormalizedL2 (originCube d m) ≤
        cubeDirichletH2RegularityVolumeL2ConstantExact d *
          (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
            (2 : ℝ≥0∞) F (by
              simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
                using hF) := by
  rcases (cubeDirichletH2RegularityExact (originCube d m)).2 u F hF hweak with
    ⟨H, hH⟩
  refine ⟨H, ?_⟩
  let V : ℝ := cubeVolume (originCube d m)
  let C : ℝ := cubeDirichletH2RegularityVolumeL2ConstantExact d
  let L : ℝ := cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F
  let hFsafe : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume := by
    simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using hF
  have hL_safe :
      (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
          (2 : ℝ≥0∞) F hFsafe = L := by
    dsimp [L]
    unfold BoundedMeasurableDomain.normalizedLpNorm
      BoundedMeasurableDomain.normalizedLpFiniteENorm
      BoundedMeasurableDomain.normalizedLpENorm
    unfold cubeLpNorm
    simp only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  have hV_pos : 0 < V := by
    dsimp [V]
    exact cubeVolume_pos (originCube d m)
  have hV_nonneg : 0 ≤ V := le_of_lt hV_pos
  have hfac_nonneg : 0 ≤ (V⁻¹) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (inv_nonneg.mpr hV_nonneg) _
  have hhilbert :
      Real.sqrt (∑ i : Fin d, ∑ j : Fin d,
        ‖H.hessCoordToScalarL2 i j‖ ^ 2) ≤ H.hessianCoordL2NormSum :=
    H.sqrt_sum_sq_hessCoordToScalarL2_le_hessianCoordL2NormSum
  have hscale :
      cubeDirichletH2RegularityConstantExact (originCube d m) =
        V ^ (1 / 2 : ℝ) * C := by
    simpa [V, C] using
      cubeDirichletH2RegularityConstantExact_eq_volume_rpow_half_mul_volumeL2ConstantExact
        (originCube d m)
  have hcancel :
      (V⁻¹) ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ) = 1 := by
    rw [Real.inv_rpow hV_nonneg (1 / 2 : ℝ)]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hV_pos _).ne'
  calc
    H.frobeniusNormalizedL2 (originCube d m)
        = (V⁻¹) ^ (1 / 2 : ℝ) *
            Real.sqrt (∑ i : Fin d, ∑ j : Fin d,
              ‖H.hessCoordToScalarL2 i j‖ ^ 2) := rfl
    _ ≤ (V⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum :=
      mul_le_mul_of_nonneg_left hhilbert hfac_nonneg
    _ ≤ (V⁻¹) ^ (1 / 2 : ℝ) *
        (cubeDirichletH2RegularityConstantExact (originCube d m) * L) :=
      mul_le_mul_of_nonneg_left hH hfac_nonneg
    _ = C * L := by
      rw [hscale]
      calc
        (V⁻¹) ^ (1 / 2 : ℝ) * (V ^ (1 / 2 : ℝ) * C * L)
            = ((V⁻¹) ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ)) * (C * L) := by ring
        _ = C * L := by rw [hcancel, one_mul]
    _ = cubeDirichletH2RegularityVolumeL2ConstantExact d *
          (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
            (2 : ℝ≥0∞) F hFsafe := by rw [hL_safe]
    _ = cubeDirichletH2RegularityVolumeL2ConstantExact d *
          (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
            (2 : ℝ≥0∞) F (by
              simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
                using hF) := by
          rfl

/-- The explicit dimension-only constant inhabits the stronger
regularity-producing centered-cube Dirichlet `q = 2` predicate. -/
theorem originCubeDirichletCalderonZygmundRegularityQTwo_exact
    (d : ℕ) [NeZero d] :
    OriginCubeDirichletCalderonZygmundRegularityQTwo d
      (cubeDirichletH2RegularityVolumeL2ConstantExact d) := by
  refine ⟨cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d, ?_⟩
  intro m u F hF hweak
  exact exists_originCube_dirichlet_calderon_zygmund_regularity_q_two m u F hF hweak

/-- The literal centered-cube `q = 2` Dirichlet Calderón--Zygmund branch in
the source: a weak Hessian is supplied as part of the `W^{2,2}` hypothesis,
and the conclusion estimates that supplied Hessian. -/
def OriginCubeDirichletCalderonZygmundQTwo (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (m : ℤ) (u : H10Function (openCubeSet (originCube d m)))
    (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function),
    H.frobeniusNormalizedL2 (originCube d m) ≤
      C * (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
        (2 : ℝ≥0∞) F (by
          simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
            using hF)

theorem OriginCubeDirichletCalderonZygmundQTwo.constant_nonneg
    {d : ℕ} {C : ℝ} (h : OriginCubeDirichletCalderonZygmundQTwo d C) :
    0 ≤ C :=
  h.1

/-- Apply the literal Dirichlet branch to a supplied weak-Hessian witness. -/
theorem OriginCubeDirichletCalderonZygmundQTwo.apply
    {d : ℕ} {C : ℝ} (h : OriginCubeDirichletCalderonZygmundQTwo d C)
    (m : ℤ) (u : H10Function (openCubeSet (originCube d m))) (F : Vec d → ℝ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function) :
    H.frobeniusNormalizedL2 (originCube d m) ≤
      C * (cubeBoundedMeasurableDomain (originCube d m)).normalizedLpNorm
        (2 : ℝ≥0∞) F (by
          simpa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
            using hF) :=
  h.2 m u F hF hweak H

/-- The explicit dimension-only constant proves the literal source-facing
Dirichlet branch.  Its implementation first produces one weak Hessian and
then uses weak-derivative uniqueness to transfer the bound to every supplied
witness. -/
theorem originCubeDirichletCalderonZygmundQTwo_exact
    (d : ℕ) [NeZero d] :
    OriginCubeDirichletCalderonZygmundQTwo d
      (cubeDirichletH2RegularityVolumeL2ConstantExact d) := by
  refine ⟨cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d, ?_⟩
  intro m u F hF hweak H
  rcases exists_originCube_dirichlet_calderon_zygmund_regularity_q_two m u F hF hweak with
    ⟨K, hK⟩
  rw [H.frobeniusNormalizedL2_eq_of_hasWeakHessianOn (originCube d m) K]
  exact hK

end CubeDirichletWeakPoissonProblem

end

end Homogenization
