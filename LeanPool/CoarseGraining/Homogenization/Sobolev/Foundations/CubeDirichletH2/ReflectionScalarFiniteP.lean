/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionL2
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeMeasureBridge

/-!
# Finite-`p` scalar transport under Dirichlet odd reflection

The scalar Dirichlet odd reflection differs from pullback by the affine cell
fold only by a sign of norm one. Combined with the measure-preserving cell fold
maps, this gives exact finite-`p` transport from a cube to its full reflection
block and exact preservation of normalized finite-`p` norms between centered
origin cubes.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

private theorem norm_cubeDirichletOddReflectionCellSign
    {d : ℕ} (choice : Fin d → Fin 3) :
    ‖cubeDirichletOddReflectionCellSign choice‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Real.norm_eq_abs, sq_abs, one_pow, pow_two,
    cubeDirichletOddReflectionCellSign_mul_self]

private theorem norm_cubeDirichletOddReflectionScalar_eq_cell
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (F : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    ‖cubeDirichletOddReflectionScalar Q F x‖ =
      ‖F (cubeFaceReflectionCellFoldMap Q choice x)‖ := by
  rw [cubeDirichletOddReflectionScalar_eq_cellScalar_of_mem_cellCube
      Q choice F hx,
    cubeDirichletOddReflectionCellScalar_apply, norm_mul,
    norm_cubeDirichletOddReflectionCellSign, one_mul]

private theorem aestronglyMeasurable_cubeDirichletOddReflectionScalar_cell
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3) (F : Vec d → ℝ)
    (hF : MeasureTheory.AEStronglyMeasurable F
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.AEStronglyMeasurable
      (cubeDirichletOddReflectionScalar Q F)
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
  have hmp : MeasureTheory.MeasurePreserving
      (cubeFaceReflectionCellFoldMap Q choice)
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice)))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using
      (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
        (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
        (openCubeSet Q)
  have hcomp : MeasureTheory.AEStronglyMeasurable
      (fun x ↦ F (cubeFaceReflectionCellFoldMap Q choice x))
      (MeasureTheory.volume.restrict
        (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    have hFmap : MeasureTheory.AEStronglyMeasurable F
        (MeasureTheory.Measure.map (cubeFaceReflectionCellFoldMap Q choice)
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice)))) := by
      rw [hmp.map_eq]
      exact hF
    simpa [Function.comp_def] using hFmap.comp_aemeasurable hmp.aemeasurable
  have hcell := hcomp.const_mul (cubeDirichletOddReflectionCellSign choice)
  refine hcell.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))] with x hx
  simpa [cubeDirichletOddReflectionCellScalar] using
    (cubeDirichletOddReflectionScalar_eq_cellScalar_of_mem_cellCube
      Q choice F hx).symm

private theorem lintegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionScalar
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (F : Vec d → ℝ) (p : FiniteLpExponent) :
    ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        ‖cubeDirichletOddReflectionScalar Q F x‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume =
      ∫⁻ y in openCubeSet Q, ‖F y‖ₑ ^
        p.exponent.toReal ∂MeasureTheory.volume := by
  calc
    ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        ‖cubeDirichletOddReflectionScalar Q F x‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume =
      ∫⁻ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        ‖F (cubeFaceReflectionCellFoldMap Q choice x)‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_openCubeSet
              (cubeFaceReflectionCellCube Q choice))] with x hx
          simpa only [ofReal_norm] using congrArg
            (fun t : ℝ ↦ ENNReal.ofReal t ^ p.exponent.toReal)
            (norm_cubeDirichletOddReflectionScalar_eq_cell Q choice F hx)
    _ = ∫⁻ y in openCubeSet Q, ‖F y‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume := by
          rw [← preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice]
          exact
            ((measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
              (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
              (openCubeSet Q)).lintegral_comp_emb
                (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
                (fun y ↦ ‖F y‖ₑ ^ p.exponent.toReal)

private theorem lintegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → ℝ)
    (p : FiniteLpExponent) :
    ∫⁻ x in cubeFaceReflectionBlockSet Q,
        ‖cubeDirichletOddReflectionScalar Q F x‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume =
      ((3 : ℝ≥0∞) ^ d) *
        ∫⁻ y in openCubeSet Q, ‖F y‖ₑ ^
          p.exponent.toReal ∂MeasureTheory.volume := by
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q,
    MeasureTheory.lintegral_iUnion]
  · simp_rw [lintegral_cubeFaceReflectionCellCube_cubeDirichletOddReflectionScalar Q]
    simp [nsmul_eq_mul]
  · intro choice
    exact measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)
  · intro choice₁ choice₂ hne
    exact disjoint_openCubeSet_cubeFaceReflectionCellCube_of_ne Q hne

private theorem finiteLpExponent_ne_zero (p : FiniteLpExponent) :
    p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (finiteLpExponent_ne_zero p) p.lt_top.ne

/-- The finite-`p` norm of the odd-reflected scalar on the full reflection
block is exactly the `3^d` measure-scaling factor times the source norm. -/
theorem eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → ℝ)
    (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm (cubeDirichletOddReflectionScalar Q F)
      p.exponent (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm F p.exponent
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (finiteLpExponent_ne_zero p) p.lt_top.ne,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (finiteLpExponent_ne_zero p) p.lt_top.ne,
    lintegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar]
  rw [ENNReal.mul_rpow_of_nonneg _ _
    (one_div_nonneg.mpr (finiteLpExponent_toReal_pos p).le)]

/-- Finite-`p` scalar integrability transports from a cube to the complete
Dirichlet odd-reflection block. -/
theorem memLp_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (p : FiniteLpExponent)
    (hF : MeasureTheory.MemLp F p.exponent
      (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.MemLp (cubeDirichletOddReflectionScalar Q F)
      p.exponent
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
  have hae : MeasureTheory.AEStronglyMeasurable
      (cubeDirichletOddReflectionScalar Q F)
      (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice ↦
      aestronglyMeasurable_cubeDirichletOddReflectionScalar_cell
        Q choice F hF.aestronglyMeasurable
  refine ⟨hae, ?_⟩
  rw [eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar Q F p]
  refine ENNReal.mul_lt_top ?_ hF.eLpNorm_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg
    (one_div_nonneg.mpr (finiteLpExponent_toReal_pos p).le) (by simp)

/-- On a centered origin cube, the odd-reflected scalar has the same exact
unnormalized finite-`p` scaling on the parent cube. -/
theorem eLpNorm_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
    {d : ℕ} {m : ℤ} (F : Vec d → ℝ) (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (cubeDirichletOddReflectionScalar (originCube d m) F)
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        MeasureTheory.eLpNorm F p.exponent
          (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict
          (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact eLpNorm_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar
    (originCube d m) F p

/-- Finite-`p` scalar integrability transports from an origin cube to its
centered parent under Dirichlet odd reflection. -/
theorem memLp_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
    {d : ℕ} {m : ℤ} {F : Vec d → ℝ} (p : FiniteLpExponent)
    (hF : MeasureTheory.MemLp F p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m)))) :
    MeasureTheory.MemLp
      (cubeDirichletOddReflectionScalar (originCube d m) F)
      p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1)))) := by
  have hmeasure :
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m + 1))) =
        MeasureTheory.volume.restrict
          (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using MeasureTheory.Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure]
  exact memLp_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar
    (originCube d m) p hF

private theorem normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet
    {d : ℕ} (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube]

private theorem restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure
    {d : ℕ} (m : ℤ) :
    MeasureTheory.volume.restrict (openCubeSet (originCube d m)) =
      ENNReal.ofReal (cubeVolume (originCube d m)) •
        normalizedCubeMeasure (originCube d m) := by
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos _)]
  rw [smul_smul]
  have hnonzero : ENNReal.ofReal (cubeVolume (originCube d m)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (cubeVolume_pos _)
  have hone : ENNReal.ofReal (cubeVolume (originCube d m)) *
      (ENNReal.ofReal (cubeVolume (originCube d m)))⁻¹ = 1 := by
    simpa [mul_comm] using
      ENNReal.inv_mul_cancel hnonzero ENNReal.ofReal_ne_top
  rw [hone, one_smul]

private theorem cubeVolume_originCube_succ {d : ℕ} (m : ℤ) :
    cubeVolume (originCube d (m + 1)) =
      (3 : ℝ) ^ d * cubeVolume (originCube d m) := by
  simp [cubeVolume, cubeScaleFactor, originCube, zpow_add₀]
  rw [mul_pow]
  ring

private theorem normalized_originCube_reflection_factor_cancel
    {d : ℕ} (m : ℤ) (p : FiniteLpExponent) :
    ENNReal.ofReal ((cubeVolume (originCube d (m + 1)))⁻¹) ^
        (p.exponent.toReal)⁻¹ *
      ((3 : ENNReal) ^ d) ^ (p.exponent.toReal)⁻¹ =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) ^
        (p.exponent.toReal)⁻¹ := by
  let N : ℝ := (3 : ℝ) ^ d
  let V : ℝ := cubeVolume (originCube d m)
  have hN : 0 < N := by positivity
  have hV : 0 < V := cubeVolume_pos _
  have hvol : cubeVolume (originCube d (m + 1)) = N * V := by
    simpa [N, V] using cubeVolume_originCube_succ (d := d) m
  have hbase_real : (N * V)⁻¹ * N = V⁻¹ := by
    field_simp [hN.ne', hV.ne']
  have hbase : ENNReal.ofReal ((N * V)⁻¹) * ENNReal.ofReal N =
      ENNReal.ofReal V⁻¹ := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_nonneg hN.le hV.le))]
    exact congrArg ENNReal.ofReal hbase_real
  rw [hvol]
  calc
    ENNReal.ofReal ((N * V)⁻¹) ^ (p.exponent.toReal)⁻¹ *
        ((3 : ENNReal) ^ d) ^ (p.exponent.toReal)⁻¹ =
      (ENNReal.ofReal ((N * V)⁻¹) * ENNReal.ofReal N) ^
        (p.exponent.toReal)⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          congr 1
          norm_num [N]
    _ = ENNReal.ofReal V⁻¹ ^ (p.exponent.toReal)⁻¹ := by
      rw [hbase]

/-- Normalized origin-cube finite-`p` scalar norms are exactly preserved by
Dirichlet odd reflection from a cube to its centered parent. -/
theorem eLpNorm_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionScalar
    {d : ℕ} {m : ℤ} (F : Vec d → ℝ) (p : FiniteLpExponent) :
    MeasureTheory.eLpNorm
      (cubeDirichletOddReflectionScalar (originCube d m) F)
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      MeasureTheory.eLpNorm F p.exponent
        (normalizedCubeMeasure (originCube d m)) := by
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet,
    normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet,
    MeasureTheory.eLpNorm_smul_measure_of_ne_top p.lt_top.ne,
    MeasureTheory.eLpNorm_smul_measure_of_ne_top p.lt_top.ne,
    eLpNorm_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar]
  simp only [smul_eq_mul, one_div, ENNReal.toReal_inv]
  rw [← mul_assoc, normalized_originCube_reflection_factor_cancel]

/-- Finite-`p` scalar integrability is preserved by normalized origin-cube
odd-reflection transport. -/
theorem memLp_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionScalar
    {d : ℕ} {m : ℤ} {F : Vec d → ℝ} (p : FiniteLpExponent)
    (hF : MeasureTheory.MemLp F p.exponent
      (normalizedCubeMeasure (originCube d m))) :
    MeasureTheory.MemLp
      (cubeDirichletOddReflectionScalar (originCube d m) F)
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
  have hFopen : MeasureTheory.MemLp F p.exponent
      (MeasureTheory.volume.restrict (openCubeSet (originCube d m))) := by
    rw [restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure]
    exact hF.smul_measure ENNReal.ofReal_ne_top
  have hreflect :=
    memLp_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar p hFopen
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  exact hreflect.smul_measure ENNReal.ofReal_ne_top

end

end Homogenization
