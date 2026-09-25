/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ArbitraryCubeEndpoint

/-! # Regularity -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeDirichletWeakPoissonProblem

/-- The scale-indexed Dirichlet `H²` constant produced by the current
zero-trace Poincare/odd-reflection proof. -/
noncomputable def cubeDirichletH2RegularityConstantExact
    {d : ℕ} [NeZero d] (Q : TriadicCube d) : ℝ :=
  ((d : ℝ) * (d : ℝ)) *
    originCubeParentReducedSolverEnergyConstantExact d Q.scale

theorem cubeDirichletH2RegularityConstantExact_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    0 ≤ cubeDirichletH2RegularityConstantExact Q := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d))
    (originCubeParentReducedSolverEnergyConstantExact_nonneg d Q.scale)

/-- The dimension-only constant for the unnormalized open-cube `L²` forcing
version of the Dirichlet `H²` estimate. -/
noncomputable def cubeDirichletH2RegularityVolumeL2ConstantExact
    (d : ℕ) [NeZero d] : ℝ :=
  cubeDirichletH2RegularityConstantExact (originCube d 0)

theorem cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ cubeDirichletH2RegularityVolumeL2ConstantExact d := by
  exact cubeDirichletH2RegularityConstantExact_nonneg (originCube d 0)

theorem cubeDirichletH2RegularityConstantExact_eq_volume_rpow_half_mul_volumeL2ConstantExact
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    cubeDirichletH2RegularityConstantExact Q =
      (cubeVolume Q) ^ (1 / 2 : ℝ) *
        cubeDirichletH2RegularityVolumeL2ConstantExact d := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let V : ℝ := cubeVolume Q₀
  let D₂ : ℝ := (d : ℝ) * (d : ℝ)
  let K : ℝ := originCubeParentReducedSolverEnergyConstantExact d Q.scale
  let K₀ : ℝ := originCubeParentReducedSolverEnergyConstantExact d 0
  have hV_pos : 0 < V := by
    dsimp [V, Q₀]
    exact cubeVolume_pos (originCube d Q.scale)
  have hV_nonneg : 0 ≤ V := le_of_lt hV_pos
  have hcancel :
      (V⁻¹) ^ (1 / 2 : ℝ) * K = K₀ := by
    simpa [V, K, K₀, Q₀] using
      originCubeParentReducedSolverEnergyConstantExact_volume_cancel d Q.scale
  have hV_cancel :
      V ^ (1 / 2 : ℝ) * (V⁻¹) ^ (1 / 2 : ℝ) = 1 := by
    rw [Real.inv_rpow hV_nonneg (1 / 2 : ℝ)]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hV_pos _).ne'
  have hK : K = V ^ (1 / 2 : ℝ) * K₀ := by
    calc
      K = 1 * K := by ring
      _ = (V ^ (1 / 2 : ℝ) * (V⁻¹) ^ (1 / 2 : ℝ)) * K := by
            rw [hV_cancel]
      _ = V ^ (1 / 2 : ℝ) * ((V⁻¹) ^ (1 / 2 : ℝ) * K) := by
            ring
      _ = V ^ (1 / 2 : ℝ) * K₀ := by
            rw [hcancel]
  have hVQ : V = cubeVolume Q := by
    dsimp [V, Q₀]
    exact cubeVolume_originCube_same_scale Q
  calc
    cubeDirichletH2RegularityConstantExact Q
        = D₂ * K := by
          simp [cubeDirichletH2RegularityConstantExact, D₂, K]
    _ = V ^ (1 / 2 : ℝ) * (D₂ * K₀) := by
          rw [hK]
          ring
    _ =
        (cubeVolume Q) ^ (1 / 2 : ℝ) *
          cubeDirichletH2RegularityVolumeL2ConstantExact d := by
          rw [hVQ]
          dsimp [cubeDirichletH2RegularityVolumeL2ConstantExact,
            cubeDirichletH2RegularityConstantExact, D₂, K₀, originCube]

theorem originCube_sum_reducedSolverEnergyBoundExact_le_regularityConstant_mul_cubeLpNorm
    {d : ℕ} [NeZero d] {m : ℤ} {F : Vec d → ℝ} :
    (∑ i : Fin d, ∑ _j : Fin d,
        originCubeParentReducedSolverEnergyBoundExact d m F i) ≤
      cubeDirichletH2RegularityConstantExact (originCube d m) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
  let K : ℝ := originCubeParentReducedSolverEnergyConstantExact d m
  let L : ℝ := cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F
  have hsum_eq :
      (∑ i : Fin d, ∑ _j : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d m F i) =
        ((d : ℝ) * (d : ℝ)) * (K * L) := by
    calc
      (∑ i : Fin d, ∑ _j : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d m F i)
          = ∑ i : Fin d, ∑ _j : Fin d, K * L := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              refine Finset.sum_congr rfl ?_
              intro _j _hj
              simpa [K, L] using
                originCubeParentReducedSolverEnergyBoundExact_eq_constant_mul_cubeLpNorm
                  d m F i
      _ = ((d : ℝ) * (d : ℝ)) * (K * L) := by
            simp
            ring
  exact le_of_eq (by
    calc
      (∑ i : Fin d, ∑ _j : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d m F i)
          = ((d : ℝ) * (d : ℝ)) * (K * L) := hsum_eq
      _ =
          cubeDirichletH2RegularityConstantExact (originCube d m) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
            simp [cubeDirichletH2RegularityConstantExact, K, L, originCube]
            ring_nf)

/-- Scale-indexed cube Dirichlet `H²` regularity obtained from odd reflection,
the parent-cube interior estimate, and the chosen zero-trace Poincare
constant. -/
theorem cubeDirichletH2RegularityExact
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubeDirichletH2Regularity Q
      (cubeDirichletH2RegularityConstantExact Q) := by
  refine ⟨cubeDirichletH2RegularityConstantExact_nonneg Q, ?_⟩
  intro u F hF hweak
  rcases
    hweak.exists_hasWeakHessianOn_cube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBoundExact
      hF with
    ⟨_uP, _huP_toFun, _huP_grad, H, hH⟩
  refine ⟨H, hH.trans ?_⟩
  let z : Vec d := triadicCubeShift Q
  let F₀ : Vec d → ℝ := fun x => F (x + z)
  have hsum :
      (∑ i : Fin d, ∑ _j : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d Q.scale F₀ i) ≤
        cubeDirichletH2RegularityConstantExact (originCube d Q.scale) *
          cubeLpNorm (originCube d Q.scale) (2 : ℝ≥0∞) F₀ :=
    originCube_sum_reducedSolverEnergyBoundExact_le_regularityConstant_mul_cubeLpNorm
      (m := Q.scale) (F := F₀)
  have hnorm := cubeLpNorm_originCube_comp_addRight_eq_of_memLp Q hF
  simpa [cubeDirichletH2RegularityConstantExact, F₀, z, hnorm] using! hsum

/-- Dimension-only cube Dirichlet `H²` regularity when the forcing is measured
in the unnormalized open-cube `L²` norm. -/
theorem cubeDirichletH2RegularityVolumeL2Exact
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubeDirichletH2RegularityVolumeL2 Q
      (cubeDirichletH2RegularityVolumeL2ConstantExact d) := by
  refine ⟨cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d, ?_⟩
  intro u F hF hweak
  rcases (cubeDirichletH2RegularityExact Q).2 u F hF hweak with ⟨H, hH⟩
  refine ⟨H, hH.trans ?_⟩
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let Cvol : ℝ := cubeDirichletH2RegularityVolumeL2ConstantExact d
  let hFopen := memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hCscale :
      cubeDirichletH2RegularityConstantExact Q =
        (cubeVolume Q) ^ (1 / 2 : ℝ) * Cvol := by
    simpa [Cvol] using
      cubeDirichletH2RegularityConstantExact_eq_volume_rpow_half_mul_volumeL2ConstantExact Q
  have hnorm :
      ‖toScalarL2 hFopen‖ =
        (cubeVolume Q) ^ (1 / 2 : ℝ) * L := by
    simpa [L, hFopen] using
      norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two Q hF
  calc
    cubeDirichletH2RegularityConstantExact Q *
        cubeLpNorm Q (2 : ℝ≥0∞) F
        = ((cubeVolume Q) ^ (1 / 2 : ℝ) * Cvol) * L := by
          rw [hCscale]
    _ = Cvol * ((cubeVolume Q) ^ (1 / 2 : ℝ) * L) := by
          ring
    _ = Cvol * ‖toScalarL2 hFopen‖ := by
          rw [hnorm]
    _ ≤
        cubeDirichletH2RegularityVolumeL2ConstantExact d *
          ‖toScalarL2 (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF)‖ := by
          exact le_rfl

/-- There exists a dimension-only constant for the unnormalized open-cube
`L²` Dirichlet `H²` estimate. -/
theorem exists_cubeDirichletH2RegularityVolumeL2InDimension
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, CubeDirichletH2RegularityVolumeL2InDimension d C := by
  refine ⟨cubeDirichletH2RegularityVolumeL2ConstantExact d, ?_⟩
  exact ⟨cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d,
    fun Q => cubeDirichletH2RegularityVolumeL2Exact Q⟩

end CubeDirichletWeakPoissonProblem

end

end Homogenization
