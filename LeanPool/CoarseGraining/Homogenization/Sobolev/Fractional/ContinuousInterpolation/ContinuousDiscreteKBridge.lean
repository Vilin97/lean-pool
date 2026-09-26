/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.KFunctional
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.KInfimum
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# Exact continuous-to-discrete unit-cube K-functional bridge

This module identifies the two genuine coordinatewise `H¹` competitor spaces
on the origin unit cube, and compares their residual and gradient quantities.
The resulting inequalities are internal transport facts for the finite-depth
continuous interpolation argument.
-/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-- Regard a continuous source competitor as an internal cube competitor on
the origin unit cube. -/
def ContinuousKCompetitor.toCubeVectorH1Function {d : ℕ}
    (G : ContinuousKCompetitor d) : CubeVectorH1Function (originCube d 0) where
  coord := G.coord

/-- Regard an internal origin-unit-cube competitor as a continuous source
competitor. -/
def CubeVectorH1Function.toContinuousKCompetitor {d : ℕ}
    (G : CubeVectorH1Function (originCube d 0)) : ContinuousKCompetitor d where
  coord := G.coord

@[simp] theorem ContinuousKCompetitor.toCubeVectorH1Function_coord {d : ℕ}
    (G : ContinuousKCompetitor d) (i : Fin d) :
    G.toCubeVectorH1Function.coord i = G.coord i := rfl

@[simp] theorem CubeVectorH1Function.toContinuousKCompetitor_coord {d : ℕ}
    (G : CubeVectorH1Function (originCube d 0)) (i : Fin d) :
    G.toContinuousKCompetitor.coord i = G.coord i := rfl

@[simp] theorem ContinuousKCompetitor.toCubeVectorH1Function_toField {d : ℕ}
    (G : ContinuousKCompetitor d) :
    G.toCubeVectorH1Function.toField = G.toField := rfl

@[simp] theorem CubeVectorH1Function.toContinuousKCompetitor_toField {d : ℕ}
    (G : CubeVectorH1Function (originCube d 0)) :
    G.toContinuousKCompetitor.toField = G.toField := rfl

@[simp] theorem ContinuousKCompetitor.toCubeVectorH1Function_grad_apply {d : ℕ}
    (G : ContinuousKCompetitor d) (x : Vec d) (i j : Fin d) :
    (G.toCubeVectorH1Function.coord i).grad x j = G.gradient x i j := rfl

@[simp] theorem CubeVectorH1Function.toContinuousKCompetitor_gradient_apply {d : ℕ}
    (G : CubeVectorH1Function (originCube d 0)) (x : Vec d) (i j : Fin d) :
    G.toContinuousKCompetitor.gradient x i j = (G.coord i).grad x j := rfl

@[simp] theorem ContinuousKCompetitor.toCubeVectorH1Function_toContinuousKCompetitor
    {d : ℕ} (G : ContinuousKCompetitor d) :
    G.toCubeVectorH1Function.toContinuousKCompetitor = G := by
  cases G
  rfl

@[simp] theorem CubeVectorH1Function.toContinuousKCompetitor_toCubeVectorH1Function
    {d : ℕ} (G : CubeVectorH1Function (originCube d 0)) :
    G.toContinuousKCompetitor.toCubeVectorH1Function = G := by
  cases G
  rfl

/-- On the unit cube, the internal cube normalization is exactly the source
normalized volume. -/
theorem normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume
    (d : ℕ) :
    normalizedCubeMeasure (originCube d 0) = (unitCenteredCubeDomain d).normalizedVolume :=
  (unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure d).symm

/-- On the origin unit cube the normalized cube measure is literally volume
restricted to the analytic open cube. -/
theorem normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet
    (d : ℕ) :
    normalizedCubeMeasure (originCube d 0) =
      volumeMeasureOn (openCubeSet (originCube d 0)) := by
  rw [normalizedCubeMeasure, cubeVolume_originCube_zero]
  simp only [inv_one, ENNReal.ofReal_one, one_smul]
  exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d 0)

/-- The scale factor of the origin unit cube is one. -/
theorem cubeScaleFactor_originCube_zero (d : ℕ) :
    cubeScaleFactor (originCube d 0) = 1 := by
  simp only [cubeScaleFactor_originCube, zpow_zero]

/-- The internal relative gradient size has no additional geometric factor on
the origin unit cube. -/
@[simp] theorem CubeVectorH1Function.relativeGradientCoordL2NormSum_originCube_zero
    {d : ℕ} (G : CubeVectorH1Function (originCube d 0)) :
    G.relativeGradientCoordL2NormSum = G.gradientCoordL2NormSum := by
  simp only [CubeVectorH1Function.relativeGradientCoordL2NormSum,
    cubeScaleFactor_originCube_zero, cubeVolume_originCube_zero]
  norm_num

/-- On the unit cube, the internal ambient-norm residual is bounded by the
source Euclidean residual. -/
theorem cubeResidualNorm_le_continuousKResidualNorm {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (G : ContinuousKCompetitor d) :
    cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
        (fun x => F x - G.toCubeVectorH1Function.toField x) ≤
      continuousKResidualNorm F G := by
  have hmem : MeasureTheory.MemLp
      (fun x => euclideanNorm (F x - G.toField x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume := by
    have hsub := F.euclideanMemL2.sub G.euclideanMemL2
    simpa only [euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec, PiLp.toLp_apply,
      Pi.sub_apply] using! hsub.norm
  change
    (MeasureTheory.eLpNorm
      (fun x => F x - G.toField x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d 0))).toReal ≤
      (MeasureTheory.eLpNorm
        (fun x => euclideanNorm (F x - G.toField x)) (2 : ℝ≥0∞)
        (unitCenteredCubeDomain d).normalizedVolume).toReal
  rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  apply ENNReal.toReal_mono hmem.eLpNorm_ne_top
  apply MeasureTheory.eLpNorm_mono
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _)] using
    norm_le_euclideanNorm (F x - G.toField x)

/-- On the unit cube, the source Euclidean residual is bounded by a positive
all-dimension multiple of the internal ambient-norm residual. -/
theorem continuousKResidualNorm_le_dimPlusOne_mul_cubeResidualNorm {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (G : ContinuousKCompetitor d) :
    continuousKResidualNorm F G ≤
      (d + 1 : ℝ) * cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
        (fun x => F x - G.toCubeVectorH1Function.toField x) := by
  let R : Vec d → Vec d := fun x => F x - G.toField x
  let C : ℝ := d + 1
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hR_vec_mem : MeasureTheory.MemLp R (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume := by
    apply MeasureTheory.MemLp.of_eval
    intro i
    have hF := F.euclideanMemL2
    rw [MeasureTheory.memLp_piLp_iff] at hF
    have hG := G.euclideanMemL2
    rw [MeasureTheory.memLp_piLp_iff] at hG
    simpa only [R, Pi.sub_apply, HilbertVec.ofVec, PiLp.toLp_apply] using!
      (hF i).sub (hG i)
  have hbound : ∀ x : Vec d, euclideanNorm (R x) ≤ ‖C • R x‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nonneg]
    calc
      euclideanNorm (R x) ≤ (d : ℝ) * ‖R x‖ :=
        euclideanNorm_le_dimension_mul_norm (R x)
      _ ≤ C * ‖R x‖ := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C]
          norm_num
        · exact norm_nonneg _
  change
    (MeasureTheory.eLpNorm (fun x => euclideanNorm (R x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume).toReal ≤
      C * (MeasureTheory.eLpNorm R (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d 0))).toReal
  rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  calc
    (MeasureTheory.eLpNorm (fun x => euclideanNorm (R x)) (2 : ℝ≥0∞)
        (unitCenteredCubeDomain d).normalizedVolume).toReal
        ≤ (MeasureTheory.eLpNorm (fun x => C • R x) (2 : ℝ≥0∞)
          (unitCenteredCubeDomain d).normalizedVolume).toReal :=
      ENNReal.toReal_mono
        ((hR_vec_mem.const_smul C).eLpNorm_ne_top)
        (by
          apply MeasureTheory.eLpNorm_mono
          intro x
          simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _)] using
            hbound x)
    _ = C * (MeasureTheory.eLpNorm R (2 : ℝ≥0∞)
        (unitCenteredCubeDomain d).normalizedVolume).toReal := by
      rw [show (fun x => C • R x) = C • R by rfl,
        MeasureTheory.eLpNorm_const_smul, ENNReal.toReal_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg hC_nonneg]

/-- The internal coordinate-summed gradient norm is the corresponding finite
sum of normalized unit-cube `L²` coordinate norms. -/
theorem CubeVectorH1Function.gradientCoordL2NormSum_eq_sum_normalizedELpNorm
    {d : ℕ} (G : CubeVectorH1Function (originCube d 0)) :
    G.gradientCoordL2NormSum =
      ∑ i : Fin d, ∑ j : Fin d,
        (MeasureTheory.eLpNorm (fun x => (G.coord i).grad x j) (2 : ℝ≥0∞)
          (normalizedCubeMeasure (originCube d 0))).toReal := by
  unfold CubeVectorH1Function.gradientCoordL2NormSum H1Function.gradientCoordL2NormSum
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
  simp [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
    MeasureTheory.Lp.norm_toLp, volumeMeasureOn]

/-- The Frobenius `L²` gradient quantity of a continuous competitor is bounded
by the relative coordinate-summed internal gradient quantity on the unit
cube. -/
theorem continuousKGradientNorm_le_cubeRelativeGradientCoordL2NormSum {d : ℕ}
    (G : ContinuousKCompetitor d) :
    continuousKGradientNorm G ≤
      G.toCubeVectorH1Function.relativeGradientCoordL2NormSum := by
  let Q : TriadicCube d := originCube d 0
  let μ : MeasureTheory.Measure (Vec d) := normalizedCubeMeasure Q
  let f : Fin d → Fin d → Vec d → ℝ := fun i j x => (G.coord i).grad x j
  let row : Fin d → Vec d → ℝ := fun i x => ∑ j : Fin d, ‖f i j x‖
  let total : Vec d → ℝ := fun x => ∑ i : Fin d, row i x
  have hcoord : ∀ i j : Fin d, MeasureTheory.MemLp (f i j) (2 : ℝ≥0∞) μ := by
    intro i j
    dsimp [f, μ, Q]
    exact (G.coord i).grad_memL2_normalizedCubeMeasure j
  have hrow_eq : ∀ i : Fin d, row i = ∑ j : Fin d, fun x => ‖f i j x‖ := by
    intro i
    funext x
    simp only [row, Finset.sum_apply]
  have htotal_eq : total = ∑ i : Fin d, row i := by
    funext x
    simp only [total, Finset.sum_apply]
  have hrow_meas : ∀ i : Fin d, MeasureTheory.AEStronglyMeasurable (row i) μ := by
    intro i
    rw [hrow_eq i]
    exact Finset.aestronglyMeasurable_sum (s := Finset.univ)
      (fun j _ => (hcoord i j).norm.aestronglyMeasurable)
  have hrow_bound : ∀ i : Fin d,
      MeasureTheory.eLpNorm (row i) (2 : ℝ≥0∞) μ ≤
        ∑ j : Fin d, MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ := by
    intro i
    rw [hrow_eq i]
    calc
      MeasureTheory.eLpNorm (∑ j : Fin d, fun x => ‖f i j x‖) (2 : ℝ≥0∞) μ
          ≤ ∑ j : Fin d,
              MeasureTheory.eLpNorm (fun x => ‖f i j x‖) (2 : ℝ≥0∞) μ :=
            MeasureTheory.eLpNorm_sum_le
              (fun j _ => (hcoord i j).norm.aestronglyMeasurable) (by norm_num)
      _ = ∑ j : Fin d, MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ := by
            apply Finset.sum_congr rfl
            intro j _
            exact MeasureTheory.eLpNorm_norm (f i j)
  have htotal_bound : MeasureTheory.eLpNorm total (2 : ℝ≥0∞) μ ≤
      ∑ i : Fin d, ∑ j : Fin d, MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ := by
    calc
      MeasureTheory.eLpNorm total (2 : ℝ≥0∞) μ
          ≤ ∑ i : Fin d, MeasureTheory.eLpNorm (row i) (2 : ℝ≥0∞) μ := by
            rw [htotal_eq]
            exact MeasureTheory.eLpNorm_sum_le
              (fun i _ => hrow_meas i) (by norm_num)
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ := by
            apply Finset.sum_le_sum
            intro i _
            exact hrow_bound i
  have hfrob_bound : MeasureTheory.eLpNorm
      (fun x => matrixFrobeniusMagnitude (G.gradient x)) (2 : ℝ≥0∞) μ ≤
      MeasureTheory.eLpNorm total (2 : ℝ≥0∞) μ := by
    apply MeasureTheory.eLpNorm_mono
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (matrixFrobeniusMagnitude_nonneg _)]
    have htotal_nonneg : 0 ≤ total x := by
      dsimp [total, row]
      exact Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg htotal_nonneg]
    simpa only [total, row, f] using! matrixFrobeniusMagnitude_le_sum_abs (G.gradient x)
  have hsum_ne_top :
      (∑ i : Fin d, ∑ j : Fin d,
        MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ) ≠ ∞ := by
    refine ENNReal.sum_ne_top.mpr ?_
    intro i _
    refine ENNReal.sum_ne_top.mpr ?_
    intro j _
    exact (hcoord i j).eLpNorm_ne_top
  rw [CubeVectorH1Function.relativeGradientCoordL2NormSum_originCube_zero]
  rw [CubeVectorH1Function.gradientCoordL2NormSum_eq_sum_normalizedELpNorm]
  change
    (MeasureTheory.eLpNorm
      (fun x => matrixFrobeniusMagnitude (G.gradient x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume).toReal ≤ _
  rw [← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  calc
    (MeasureTheory.eLpNorm
        (fun x => matrixFrobeniusMagnitude (G.gradient x)) (2 : ℝ≥0∞) μ).toReal
        ≤ (∑ i : Fin d, ∑ j : Fin d,
          MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ).toReal :=
      ENNReal.toReal_mono hsum_ne_top (hfrob_bound.trans htotal_bound)
    _ = ∑ i : Fin d, ∑ j : Fin d,
        (MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ).toReal := by
      rw [ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.toReal_sum]
        exact fun j _ => (hcoord i j).eLpNorm_ne_top
      · intro i _
        exact ENNReal.sum_ne_top.mpr fun j _ => (hcoord i j).eLpNorm_ne_top

/-- The relative coordinate-summed internal gradient quantity is bounded by a
positive all-dimension multiple of the source Frobenius `L²` quantity. -/
theorem cubeRelativeGradientCoordL2NormSum_le_dimPlusOne_sq_mul_continuousKGradientNorm
    {d : ℕ} (G : ContinuousKCompetitor d) :
    G.toCubeVectorH1Function.relativeGradientCoordL2NormSum ≤
      (d + 1 : ℝ) ^ 2 * continuousKGradientNorm G := by
  let Q : TriadicCube d := originCube d 0
  let μ : MeasureTheory.Measure (Vec d) := normalizedCubeMeasure Q
  let f : Fin d → Fin d → Vec d → ℝ := fun i j x => (G.coord i).grad x j
  let hFrob : Vec d → ℝ := fun x => matrixFrobeniusMagnitude (G.gradient x)
  have hFrob_mem : MeasureTheory.MemLp hFrob (2 : ℝ≥0∞) μ := by
    dsimp [hFrob, μ, Q]
    rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
    exact G.gradientFrobeniusMemL2
  have hentry : ∀ x : Vec d, ∀ i j : Fin d, |f i j x| ≤ hFrob x := by
    intro x i j
    dsimp [f, hFrob]
    apply (sq_le_sq₀ (abs_nonneg _) (matrixFrobeniusMagnitude_nonneg _)).mp
    rw [sq_abs, sq_matrixFrobeniusMagnitude]
    calc
      (G.coord i).grad x j ^ 2 ≤ ∑ l : Fin d, (G.coord i).grad x l ^ 2 :=
        Finset.single_le_sum (fun l _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ k : Fin d, ∑ l : Fin d, (G.coord k).grad x l ^ 2 :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun k => ∑ l : Fin d, (G.coord k).grad x l ^ 2)
          (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)
  have hcoord_le : ∀ i j : Fin d,
      MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ ≤
        MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞) μ := by
    intro i j
    apply MeasureTheory.eLpNorm_mono
    intro x
    have hfrob_nonneg : 0 ≤ hFrob x := by
      dsimp [hFrob]
      exact matrixFrobeniusMagnitude_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hfrob_nonneg] using hentry x i j
  have hcoord_real_le : ∀ i j : Fin d,
      (MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ).toReal ≤
        (MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞) μ).toReal := by
    intro i j
    exact ENNReal.toReal_mono hFrob_mem.eLpNorm_ne_top (hcoord_le i j)
  have hsum_le :
      (∑ i : Fin d, ∑ j : Fin d,
        (MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ).toReal) ≤
        (d : ℝ) ^ 2 * (MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞) μ).toReal := by
    calc
      (∑ i : Fin d, ∑ j : Fin d,
          (MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ).toReal)
          ≤ ∑ i : Fin d, ∑ j : Fin d,
            (MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞) μ).toReal := by
              apply Finset.sum_le_sum
              intro i _
              apply Finset.sum_le_sum
              intro j _
              exact hcoord_real_le i j
      _ = (d : ℝ) ^ 2 * (MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞) μ).toReal := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
  rw [CubeVectorH1Function.relativeGradientCoordL2NormSum_originCube_zero]
  rw [CubeVectorH1Function.gradientCoordL2NormSum_eq_sum_normalizedELpNorm]
  change _ ≤ (d + 1 : ℝ) ^ 2 *
    (MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume).toReal
  rw [← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  calc
    (∑ i : Fin d, ∑ j : Fin d,
        (MeasureTheory.eLpNorm (f i j) (2 : ℝ≥0∞) μ).toReal)
        ≤ (d : ℝ) ^ 2 * (MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞) μ).toReal := hsum_le
    _ ≤ (d + 1 : ℝ) ^ 2 * (MeasureTheory.eLpNorm hFrob (2 : ℝ≥0∞) μ).toReal := by
      apply mul_le_mul_of_nonneg_right
      · exact (sq_le_sq₀ (by positivity) (by positivity)).mpr (by norm_num)
      · exact ENNReal.toReal_nonneg

/-- One positive, all-dimension constant used uniformly in both directions of
the continuous/discrete unit-cube comparison. -/
noncomputable def continuousDiscreteKBridgeConstant (d : ℕ) : ℝ :=
  (d + 1 : ℝ) ^ 2

theorem one_le_continuousDiscreteKBridgeConstant (d : ℕ) :
    1 ≤ continuousDiscreteKBridgeConstant d := by
  unfold continuousDiscreteKBridgeConstant
  have hbase : 1 ≤ (d + 1 : ℝ) := by norm_num
  nlinarith [sq_nonneg ((d + 1 : ℝ) - 1)]

theorem continuousDiscreteKBridgeConstant_nonneg (d : ℕ) :
    0 ≤ continuousDiscreteKBridgeConstant d :=
  (zero_le_one.trans (one_le_continuousDiscreteKBridgeConstant d))

private theorem sqrt_residual_gradient_le_mul_of_endpoint_bounds
    {Aout Bout Ain Bin t C : ℝ}
    (hC : 0 ≤ C) (hAout : 0 ≤ Aout) (hBout : 0 ≤ Bout)
    (hAin : 0 ≤ Ain) (hBin : 0 ≤ Bin)
    (hA : Aout ≤ C * Ain) (hB : Bout ≤ C * Bin) :
    Real.sqrt (Aout ^ 2 + t ^ 2 * Bout ^ 2) ≤
      C * Real.sqrt (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
  have hCAin : 0 ≤ C * Ain := mul_nonneg hC hAin
  have hCBin : 0 ≤ C * Bin := mul_nonneg hC hBin
  have hA_sq : Aout ^ 2 ≤ C ^ 2 * Ain ^ 2 := by
    calc
      Aout ^ 2 ≤ (C * Ain) ^ 2 := (sq_le_sq₀ hAout hCAin).mpr hA
      _ = C ^ 2 * Ain ^ 2 := by ring
  have hB_sq : Bout ^ 2 ≤ C ^ 2 * Bin ^ 2 := by
    calc
      Bout ^ 2 ≤ (C * Bin) ^ 2 := (sq_le_sq₀ hBout hCBin).mpr hB
      _ = C ^ 2 * Bin ^ 2 := by ring
  have hsum : Aout ^ 2 + t ^ 2 * Bout ^ 2 ≤
      C ^ 2 * (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
    calc
      Aout ^ 2 + t ^ 2 * Bout ^ 2
          ≤ C ^ 2 * Ain ^ 2 + t ^ 2 * (C ^ 2 * Bin ^ 2) :=
            add_le_add hA_sq (mul_le_mul_of_nonneg_left hB_sq (sq_nonneg t))
      _ = C ^ 2 * (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by ring
  calc
    Real.sqrt (Aout ^ 2 + t ^ 2 * Bout ^ 2)
        ≤ Real.sqrt (C ^ 2 * (Ain ^ 2 + t ^ 2 * Bin ^ 2)) :=
          Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (C ^ 2) * Real.sqrt (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg C)]
    _ = C * Real.sqrt (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
          rw [Real.sqrt_sq hC]

/-- Sending a continuous competitor to the internal cube competitor changes
its exact K-functional value by at most the bridge constant. -/
theorem cubeKFunctionalCompetitorValue_le_continuousKFunctionalCompetitorValue_mul
    {d : ℕ} (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) :
    cubeVectorKFunctionalCompetitorValue (originCube d 0) t.1 F
      G.toCubeVectorH1Function ≤
      continuousDiscreteKBridgeConstant d * continuousKFunctionalCompetitorValue t F G := by
  let C : ℝ := continuousDiscreteKBridgeConstant d
  have hC : 0 ≤ C := continuousDiscreteKBridgeConstant_nonneg d
  have hC_one : 1 ≤ C := one_le_continuousDiscreteKBridgeConstant d
  have hA :
      cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
          (fun x => F x - G.toCubeVectorH1Function.toField x) ≤
        C * continuousKResidualNorm F G := by
    calc
      cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
          (fun x => F x - G.toCubeVectorH1Function.toField x)
          ≤ continuousKResidualNorm F G := cubeResidualNorm_le_continuousKResidualNorm F G
      _ ≤ C * continuousKResidualNorm F G := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC_one
          (continuousKResidualNorm_nonneg F G)
  have hB : G.toCubeVectorH1Function.relativeGradientCoordL2NormSum ≤
      C * continuousKGradientNorm G := by
    simpa only [C] using!
      cubeRelativeGradientCoordL2NormSum_le_dimPlusOne_sq_mul_continuousKGradientNorm G
  simpa only [cubeVectorKFunctionalCompetitorValue,
    continuousKFunctionalCompetitorValue] using
    sqrt_residual_gradient_le_mul_of_endpoint_bounds hC
      (cubeLpNorm_nonneg (originCube d 0) (2 : ℝ≥0∞) _)
      G.toCubeVectorH1Function.relativeGradientCoordL2NormSum_nonneg
      (continuousKResidualNorm_nonneg F G) (continuousKGradientNorm_nonneg G)
      hA hB

/-- Sending an internal cube competitor to the continuous source competitor
changes its exact K-functional value by at most the bridge constant. -/
theorem continuousKFunctionalCompetitorValue_le_cubeKFunctionalCompetitorValue_mul
    {d : ℕ} (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d)
    (G : CubeVectorH1Function (originCube d 0)) :
    continuousKFunctionalCompetitorValue t F G.toContinuousKCompetitor ≤
      continuousDiscreteKBridgeConstant d *
        cubeVectorKFunctionalCompetitorValue (originCube d 0) t.1 F G := by
  let C : ℝ := continuousDiscreteKBridgeConstant d
  have hC : 0 ≤ C := continuousDiscreteKBridgeConstant_nonneg d
  have hC_one : 1 ≤ C := one_le_continuousDiscreteKBridgeConstant d
  have hsmall : (d + 1 : ℝ) ≤ C := by
    dsimp [C, continuousDiscreteKBridgeConstant]
    have hbase : 1 ≤ (d + 1 : ℝ) := by norm_num
    nlinarith [sq_nonneg ((d + 1 : ℝ) - 1)]
  have hA : continuousKResidualNorm F G.toContinuousKCompetitor ≤
      C * cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
        (fun x => F x - G.toField x) := by
    calc
      continuousKResidualNorm F G.toContinuousKCompetitor
          ≤ (d + 1 : ℝ) * cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
            (fun x => F x - G.toField x) := by
              simpa only using!
                continuousKResidualNorm_le_dimPlusOne_mul_cubeResidualNorm F
                  G.toContinuousKCompetitor
      _ ≤ C * cubeLpNorm (originCube d 0) (2 : ℝ≥0∞)
            (fun x => F x - G.toField x) :=
          mul_le_mul_of_nonneg_right hsmall
            (cubeLpNorm_nonneg (originCube d 0) (2 : ℝ≥0∞) _)
  have hB : continuousKGradientNorm G.toContinuousKCompetitor ≤
      C * G.relativeGradientCoordL2NormSum := by
    calc
      continuousKGradientNorm G.toContinuousKCompetitor
          ≤ G.relativeGradientCoordL2NormSum := by
              simpa only using!
                continuousKGradientNorm_le_cubeRelativeGradientCoordL2NormSum
                  G.toContinuousKCompetitor
      _ ≤ C * G.relativeGradientCoordL2NormSum := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC_one
          G.relativeGradientCoordL2NormSum_nonneg
  simpa only [cubeVectorKFunctionalCompetitorValue,
    continuousKFunctionalCompetitorValue] using
    sqrt_residual_gradient_le_mul_of_endpoint_bounds hC
      (continuousKResidualNorm_nonneg F G.toContinuousKCompetitor)
      (continuousKGradientNorm_nonneg G.toContinuousKCompetitor)
      (cubeLpNorm_nonneg (originCube d 0) (2 : ℝ≥0∞) _)
      G.relativeGradientCoordL2NormSum_nonneg hA hB

private theorem exists_cubeVectorH1Function_value_le_add {d : ℕ}
    (t : ℝ) (F : Vec d → Vec d) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : CubeVectorH1Function (originCube d 0),
      cubeVectorKFunctionalCompetitorValue (originCube d 0) t F G ≤
        cubeVectorKFunctional (originCube d 0) t F + ε := by
  unfold cubeVectorKFunctional
  obtain ⟨a, ⟨G, rfl⟩, ha⟩ :=
    (csInf_lt_iff (cubeVectorKFunctional_range_bddBelow (originCube d 0) t F)
      (cubeVectorKFunctional_range_nonempty (originCube d 0) t F)).1
      (lt_add_of_pos_right _ hε)
  exact ⟨G, ha.le⟩

/-- The internal discrete K-functional is bounded by the exact continuous
K-functional at every source scale, with a d=0-safe constant. -/
theorem cubeVectorKFunctional_le_mul_continuousKFunctional {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    cubeVectorKFunctional (originCube d 0) t.1 F ≤
      continuousDiscreteKBridgeConstant d * continuousKFunctional t F := by
  let C : ℝ := continuousDiscreteKBridgeConstant d
  have hC_one : 1 ≤ C := one_le_continuousDiscreteKBridgeConstant d
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_one
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨G, hG⟩ :=
    exists_continuousKCompetitor_value_le_add t F (div_pos hε hC_pos)
  calc
    cubeVectorKFunctional (originCube d 0) t.1 F
        ≤ cubeVectorKFunctionalCompetitorValue (originCube d 0) t.1 F
          G.toCubeVectorH1Function :=
            cubeVectorKFunctional_le_competitor (originCube d 0) t.1 F _
    _ ≤ C * continuousKFunctionalCompetitorValue t F G := by
      simpa only [C] using
        cubeKFunctionalCompetitorValue_le_continuousKFunctionalCompetitorValue_mul t F G
    _ ≤ C * (continuousKFunctional t F + ε / C) :=
      mul_le_mul_of_nonneg_left hG (le_of_lt hC_pos)
    _ = C * continuousKFunctional t F + ε := by
      field_simp [hC_ne]

/-- The exact continuous K-functional is bounded by the internal discrete
K-functional at every source scale, with the same d=0-safe constant. -/
theorem continuousKFunctional_le_mul_cubeVectorKFunctional {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t F ≤
      continuousDiscreteKBridgeConstant d * cubeVectorKFunctional (originCube d 0) t.1 F := by
  let C : ℝ := continuousDiscreteKBridgeConstant d
  have hC_one : 1 ≤ C := one_le_continuousDiscreteKBridgeConstant d
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_one
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨G, hG⟩ :=
    exists_cubeVectorH1Function_value_le_add t.1 F (div_pos hε hC_pos)
  calc
    continuousKFunctional t F
        ≤ continuousKFunctionalCompetitorValue t F G.toContinuousKCompetitor :=
          continuousKFunctional_le_competitor t F _
    _ ≤ C * cubeVectorKFunctionalCompetitorValue (originCube d 0) t.1 F G := by
      simpa only [C] using
        continuousKFunctionalCompetitorValue_le_cubeKFunctionalCompetitorValue_mul t F G
    _ ≤ C * (cubeVectorKFunctional (originCube d 0) t.1 F + ε / C) :=
      mul_le_mul_of_nonneg_left hG (le_of_lt hC_pos)
    _ = C * cubeVectorKFunctional (originCube d 0) t.1 F + ε := by
      field_simp [hC_ne]

end

end Homogenization
