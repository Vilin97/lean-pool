/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.OverlapDefinitions
import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlapEuclidean
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# Fractional Poincare estimate from the exact overlap norm

The depth-zero term of the exact overlapping `p = q = 2` Besov seminorm is
the normalized `L²` fluctuation on the root cube.  Combining this observation
coordinatewise with the Hilbert-valued `L²` triangle inequality proves the
fractional Poincare estimate directly, without importing a Sobolev embedding.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- A concrete Euclidean `L²` fact on a triadic cube supplies all coordinate
integrability certificates required by the exact overlap kernel. -/
theorem exactOverlapEuclideanIntegrable_of_euclidean_memLp {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    ExactOverlapEuclideanIntegrable Q F where
  coordinate := fun i => by
    have hi : MemLp (fun x => F x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
      simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF.eval_piLp i
    exact
      { root := hi.integrable (by norm_num)
        overlap := fun _ _ hS =>
          (ScalarOverlap.memLp_of_mem_centersAtDepth_of_memLp hS hi).integrable
            (by norm_num) }

private theorem enorm_ofVec_sq_eq_sum_enorm_sq {d : ℕ} (v : Vec d) :
    ‖HilbertVec.ofVec v‖ₑ ^ (2 : ℕ) = ∑ i : Fin d, ‖v i‖ₑ ^ (2 : ℕ) := by
  rw [← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [HilbertVec.norm_sq_eq_sum_sq]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg (v i)), sq_abs]

private theorem eLpNorm_two_sq {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {μ : Measure (Vec d)} (f : Vec d → E) :
    (eLpNorm f (2 : ℝ≥0∞) μ) ^ (2 : ℕ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  rw [← ENNReal.rpow_natCast]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem eLpNorm_hilbertVec_two_eq_coordinateENorm {d : ℕ}
    {μ : Measure (Vec d)} (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) μ) :
    eLpNorm (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) μ =
      (∑ i : Fin d, (eLpNorm (fun x => F x i) (2 : ℝ≥0∞) μ) ^ 2) ^
        ((2 : ℝ)⁻¹) := by
  have henergy :
      (eLpNorm (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) μ) ^ (2 : ℕ) =
        ∑ i : Fin d, (eLpNorm (fun x => F x i) (2 : ℝ≥0∞) μ) ^ 2 := by
    rw [eLpNorm_two_sq (fun x => HilbertVec.ofVec (F x))]
    calc
      (∫⁻ x, ‖HilbertVec.ofVec (F x)‖ₑ ^ (2 : ℕ) ∂μ) =
          ∫⁻ x, ∑ i : Fin d, ‖F x i‖ₑ ^ (2 : ℕ) ∂μ := by
        apply lintegral_congr
        intro x
        exact enorm_ofVec_sq_eq_sum_enorm_sq (F x)
      _ = ∑ i : Fin d, ∫⁻ x, ‖F x i‖ₑ ^ (2 : ℕ) ∂μ := by
        rw [lintegral_finsetSum']
        intro i _
        exact (hF.eval_piLp i).aestronglyMeasurable.enorm.pow_const (2 : ℕ)
      _ = ∑ i : Fin d, (eLpNorm (fun x => F x i) (2 : ℝ≥0∞) μ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact (eLpNorm_two_sq (fun x => F x i)).symm
  calc
    eLpNorm (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) μ =
        ((eLpNorm (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) μ) ^
          (2 : ℕ)) ^ ((2 : ℝ)⁻¹) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ = (∑ i : Fin d, (eLpNorm (fun x => F x i) (2 : ℝ≥0∞) μ) ^ 2) ^
        ((2 : ℝ)⁻¹) := by
      rw [henergy]

private theorem exactOverlapDepthAverage_two_zero {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapDepthAverage Q 2 u hu 0 =
      (exactOverlapLocalOscillation (ScalarOverlap.middleChildCube Q) 2 u
        (hu.overlap 0 _ (by simp))) ^ (2 : ℝ) := by
  let D := ScalarOverlap.centersAtDepth Q 0
  let g : TriadicCube d → ℝ≥0∞ := fun S =>
    if hS : S ∈ D then
      (exactOverlapLocalOscillation S 2 u (hu.overlap 0 S hS)) ^ (2 : ℝ)
    else 0
  rw [exactOverlapDepthAverage_eq]
  have hsum : D.attach.sum (fun S =>
      (exactOverlapLocalOscillation S.1 (ENNReal.ofReal 2) u
        (hu.overlap 0 S.1 S.2)) ^ (2 : ℝ)) = D.sum g := by
    calc
      D.attach.sum (fun S =>
          (exactOverlapLocalOscillation S.1 (ENNReal.ofReal 2) u
            (hu.overlap 0 S.1 S.2)) ^ (2 : ℝ)) =
          D.attach.sum (fun S => g S.1) := by
        apply Finset.sum_congr rfl
        intro S _
        simp only [g, dif_pos S.2]
        norm_num
      _ = D.sum g := Finset.sum_attach D g
  change ((D.card : ℝ≥0∞)⁻¹) *
      D.attach.sum (fun S =>
        (exactOverlapLocalOscillation S.1 (ENNReal.ofReal 2) u
          (hu.overlap 0 S.1 S.2)) ^ (2 : ℝ)) = _
  rw [hsum]
  simp only [D, ScalarOverlap.centersAtDepth_zero, Finset.card_singleton,
    Nat.cast_one, inv_one, one_mul, Finset.sum_singleton, g,
    dif_pos (Finset.mem_singleton_self _)]

private theorem exactOverlapDepthTerm_two_zero {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapDepthTerm Q s.1 2 u hu 0 =
      exactOverlapRootWeight Q s.1 *
        exactOverlapLocalOscillation (ScalarOverlap.middleChildCube Q) 2 u
          (hu.overlap 0 _ (by simp)) := by
  rw [exactOverlapDepthTerm_eq, exactOverlapDepthAverage_two_zero,
    exactOverlapDepthWeight_zero]
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem exactOverlapRootWeight_mul_localOscillation_le_finiteSeminorm
    {d : ℕ} (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapRootWeight Q s.1 *
        exactOverlapLocalOscillation (ScalarOverlap.middleChildCube Q) 2 u
          (hu.overlap 0 _ (by simp)) ≤
      exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q u hu := by
  rw [← exactOverlapDepthTerm_two_zero]
  rw [exactOverlapFiniteSeminorm_eq]
  change exactOverlapDepthTerm Q s.1 2 u hu 0 ≤
    (∑' j : ℕ, (exactOverlapDepthTerm Q s.1 2 u hu j) ^ (2 : ℝ)) ^
      ((2 : ℝ)⁻¹)
  calc
    exactOverlapDepthTerm Q s.1 2 u hu 0 =
        ((exactOverlapDepthTerm Q s.1 2 u hu 0) ^ (2 : ℝ)) ^
          ((2 : ℝ)⁻¹) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    _ ≤ (∑' j : ℕ, (exactOverlapDepthTerm Q s.1 2 u hu j) ^ (2 : ℝ)) ^
        ((2 : ℝ)⁻¹) := by
      apply ENNReal.rpow_le_rpow (ENNReal.le_tsum 0)
      norm_num

private theorem exactOverlapLocalOscillation_middleChildCube_two {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapLocalOscillation (ScalarOverlap.middleChildCube Q) 2 u
        (hu.overlap 0 _ (by simp)) =
      eLpNorm (fun x => u x - exactOverlapRootMean Q u hu.root) 2
        (normalizedCubeMeasure Q) := by
  unfold exactOverlapLocalOscillation
  have hmean : exactOverlapLocalMean (ScalarOverlap.middleChildCube Q) u
      (hu.overlap 0 _ (by simp)) = exactOverlapRootMean Q u hu.root := by
    unfold exactOverlapLocalMean exactOverlapRootMean
    rw [ScalarOverlap.normalizedCubeMeasure_middleChildCube]
  rw [hmean, ScalarOverlap.normalizedCubeMeasure_middleChildCube]

private theorem mul_euclideanENorm_le_euclideanENorm_of_mul_le {d : ℕ}
    (c : ℝ≥0∞) (a b : Fin d → ℝ≥0∞) (h : ∀ i, c * a i ≤ b i) :
    c * (∑ i : Fin d, a i ^ 2) ^ ((2 : ℝ)⁻¹) ≤
      (∑ i : Fin d, b i ^ 2) ^ ((2 : ℝ)⁻¹) := by
  have hsquares : c ^ 2 * ∑ i : Fin d, a i ^ 2 ≤ ∑ i : Fin d, b i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      c ^ 2 * a i ^ 2 = (c * a i) ^ 2 := by ring
      _ ≤ b i ^ 2 := pow_le_pow_left' (h i) 2
  calc
    c * (∑ i : Fin d, a i ^ 2) ^ ((2 : ℝ)⁻¹) =
        (c ^ 2 * ∑ i : Fin d, a i ^ 2) ^ ((2 : ℝ)⁻¹) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ (∑ i : Fin d, b i ^ 2) ^ ((2 : ℝ)⁻¹) := by
      apply ENNReal.rpow_le_rpow hsquares
      norm_num

private noncomputable def exactOverlapRootMeanVec {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) : Vec d :=
  fun i => exactOverlapRootMean Q (fun x => F x i) (hF.coordinate i).root

private theorem exactOverlapRootWeight_mul_rootFluctuation_le_seminorm
    {d : ℕ} (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    let hI := exactOverlapEuclideanIntegrable_of_euclidean_memLp Q F hF
    exactOverlapRootWeight Q s.1 *
        eLpNorm (fun x => HilbertVec.ofVec (F x - exactOverlapRootMeanVec Q F hI))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
      exactOverlapEuclideanSeminormTwo s Q F hI := by
  let hI := exactOverlapEuclideanIntegrable_of_euclidean_memLp Q F hF
  let M := exactOverlapRootMeanVec Q F hI
  have hresidual : MemLp (fun x => HilbertVec.ofVec (F x - M)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    have hsub := hF.sub (memLp_const (HilbertVec.ofVec M))
    simpa only [Pi.sub_apply, map_sub] using! hsub
  change exactOverlapRootWeight Q s.1 *
      eLpNorm (fun x => HilbertVec.ofVec (F x - M)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) ≤
    exactOverlapEuclideanSeminormTwo s Q F hI
  rw [eLpNorm_hilbertVec_two_eq_coordinateENorm _ hresidual,
    exactOverlapEuclideanSeminormTwo_eq]
  apply mul_euclideanENorm_le_euclideanENorm_of_mul_le
  intro i
  change exactOverlapRootWeight Q s.1 *
      eLpNorm (fun x => F x i - M i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
    exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q (fun x => F x i)
      (hI.coordinate i)
  rw [show M i = exactOverlapRootMean Q (fun x => F x i)
      (hI.coordinate i).root by rfl]
  rw [← exactOverlapLocalOscillation_middleChildCube_two Q (fun x => F x i)
    (hI.coordinate i)]
  exact exactOverlapRootWeight_mul_localOscillation_le_finiteSeminorm s Q
    (fun x => F x i) (hI.coordinate i)

private theorem eLpNorm_hilbertVec_le_residual_add_const {d : ℕ}
    {Q : TriadicCube d} (F : Vec d → Vec d) (M : Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    eLpNorm (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x - M)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) +
        eLpNorm (fun _ : Vec d => HilbertVec.ofVec M) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
  have hresidual : MemLp (fun x => HilbertVec.ofVec (F x - M)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    have hsub := hF.sub (memLp_const (HilbertVec.ofVec M))
    simpa only [Pi.sub_apply, map_sub] using! hsub
  have hadd := eLpNorm_add_le hresidual.aestronglyMeasurable
    (aestronglyMeasurable_const (b := HilbertVec.ofVec M))
    (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  rw [show (fun x => HilbertVec.ofVec (F x)) =
      (fun x => HilbertVec.ofVec (F x - M)) +
        (fun _ : Vec d => HilbertVec.ofVec M) by
    funext x
    change HilbertVec.ofVec (F x) =
      HilbertVec.ofVec (F x - M) + HilbertVec.ofVec M
    apply HilbertVec.ext
    intro i
    simp [HilbertVec.ofVec, PiLp.toLp_apply]]
  exact hadd

private theorem eLpNorm_const_rootMeanVec_eq {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hI : ExactOverlapEuclideanIntegrable Q F) :
    eLpNorm (fun _ : Vec d => HilbertVec.ofVec (exactOverlapRootMeanVec Q F hI))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) =
      exactOverlapEuclideanRootMeanENorm Q F hI := by
  let M := exactOverlapRootMeanVec Q F hI
  calc
    eLpNorm (fun _ : Vec d => HilbertVec.ofVec M) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) = ‖HilbertVec.ofVec M‖ₑ := by
      rw [eLpNorm_const _ (by norm_num) (normalizedCubeMeasure_ne_zero Q)]
      simp only [normalizedCubeMeasure_apply_univ, ENNReal.toReal_ofNat, one_div]
      simp
    _ = ENNReal.ofReal (euclideanNorm M) := by
      rw [euclideanNorm_eq_norm_ofVec, ofReal_norm]
    _ = exactOverlapEuclideanRootMeanENorm Q F hI := by
      rw [exactOverlapEuclideanRootMeanENorm_eq_ofReal_euclideanNorm]
      rfl

private theorem mul_le_add_mul_of_le_add_of_mul_le (w x y z b : ℝ≥0∞)
    (hxy : x ≤ y + z) (hy : w * y ≤ b) : w * x ≤ b + w * z := by
  calc
    w * x ≤ w * (y + z) := by gcongr
    _ = w * y + w * z := by rw [mul_add]
    _ ≤ b + w * z := by gcongr

/-- The root-weighted normalized Euclidean `L²` norm is controlled by the
exact Euclidean overlap full norm. -/
theorem exactOverlapRootWeight_mul_eLpNorm_le_exactOverlapEuclideanNormTwo
    {d : ℕ} (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    let hI := exactOverlapEuclideanIntegrable_of_euclidean_memLp Q F hF
    exactOverlapRootWeight Q s.1 *
        eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q) ≤
      exactOverlapEuclideanNormTwo s Q F hI := by
  let hI := exactOverlapEuclideanIntegrable_of_euclidean_memLp Q F hF
  let M := exactOverlapRootMeanVec Q F hI
  have htriangle := eLpNorm_hilbertVec_le_residual_add_const F M hF
  have hconstant := eLpNorm_const_rootMeanVec_eq Q F hI
  have hfluctuation :=
    exactOverlapRootWeight_mul_rootFluctuation_le_seminorm s Q F hF
  change exactOverlapRootWeight Q s.1 *
      eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q) ≤
    exactOverlapEuclideanNormTwo s Q F hI
  rw [exactOverlapEuclideanNormTwo_eq]
  calc
    exactOverlapRootWeight Q s.1 *
        eLpNorm (fun x => HilbertVec.ofVec (F x)) 2
          (normalizedCubeMeasure Q) ≤
      exactOverlapEuclideanSeminormTwo s Q F hI +
        exactOverlapRootWeight Q s.1 *
          eLpNorm (fun _ : Vec d => HilbertVec.ofVec M) 2
            (normalizedCubeMeasure Q) :=
      mul_le_add_mul_of_le_add_of_mul_le _ _ _ _ _ htriangle hfluctuation
    _ = exactOverlapEuclideanSeminormTwo s Q F hI +
        exactOverlapRootWeight Q s.1 *
          exactOverlapEuclideanRootMeanENorm Q F hI := by rw [hconstant]

namespace UnitCubeEuclideanL2Field

/-- The canonical exact-overlap integrability certificate carried by a
Euclidean `L²` field on the centered unit cube. -/
theorem exactOverlapEuclideanIntegrable {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    ExactOverlapEuclideanIntegrable (originCube d 0) F := by
  apply exactOverlapEuclideanIntegrable_of_euclidean_memLp
  rw [← unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure]
  exact F.euclideanMemL2

end UnitCubeEuclideanL2Field

/-- On the centered unit cube, the exact overlap full norm controls the
source-facing normalized Euclidean `L²` norm with constant exactly one. -/
theorem unitCube_normalizedEuclideanLpENorm_le_exactOverlapEuclideanNormTwo
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm 2 F ≤
      exactOverlapEuclideanNormTwo s (originCube d 0) F
        F.exactOverlapEuclideanIntegrable := by
  have hmem : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d 0)) := by
    rw [← unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact F.euclideanMemL2
  have h := exactOverlapRootWeight_mul_eLpNorm_le_exactOverlapEuclideanNormTwo
    s (originCube d 0) F hmem
  change eLpNorm (fun x => euclideanNorm (F x)) 2
      (unitCenteredCubeDomain d).normalizedVolume ≤ _
  rw [unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure]
  simpa only [euclideanNorm_eq_norm_ofVec, eLpNorm_norm, exactOverlapRootWeight,
    originCube, Int.cast_zero, neg_zero, zero_mul, ENNReal.rpow_zero, one_mul] using h

end

end Homogenization
