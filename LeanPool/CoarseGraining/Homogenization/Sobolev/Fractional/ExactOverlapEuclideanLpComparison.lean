/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlapEuclideanLpCoordinateBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanGagliardoCoordinateBridgeP
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapScalarPComparison
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.AssemblyPieces
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspCongruence

/-!
# Finite-`p` direct Euclidean overlap versus fractional Sobolev seminorm

This is the source-facing comparison for the canonical vector-valued overlap
seminorm.  The proof keeps its direct Euclidean local oscillations intact and
uses scalar coordinates only internally.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne

/-- The globally measurable representative selected from a direct Euclidean
`L^p` field.  It is used internally to discharge scalar real-variable
measurability conditions, while source-facing statements retain the original
field carrier. -/
noncomputable def CubeEuclideanLpField.measurableRepresentative {d : ℕ}
    {Q : TriadicCube d} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q p) : CubeEuclideanLpField Q p :=
  let f : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (F x)
  let hf : AEStronglyMeasurable f (normalizedCubeMeasure Q) :=
    F.euclideanMemLp.aestronglyMeasurable
  { toField := fun x => HilbertVec.toVec (AEStronglyMeasurable.mk f hf x)
    euclideanMemLp := by
      simpa only [HilbertVec.ofVec_toVec] using F.euclideanMemLp.ae_eq hf.ae_eq_mk }

theorem CubeEuclideanLpField.measurable_measurableRepresentative {d : ℕ}
    {Q : TriadicCube d} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q p) : Measurable F.measurableRepresentative := by
  let : MeasurableSpace (HilbertVec d) := borel (HilbertVec d)
  let : BorelSpace (HilbertVec d) := ⟨rfl⟩
  unfold measurableRepresentative
  dsimp only
  exact (HilbertVec.continuousLinearEquivVec d).continuous.measurable.comp
    F.euclideanMemLp.aestronglyMeasurable.measurable_mk

theorem CubeEuclideanLpField.ae_eq_measurableRepresentative {d : ℕ}
    {Q : TriadicCube d} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q p) :
    F =ᵐ[normalizedCubeMeasure Q] F.measurableRepresentative := by
  unfold measurableRepresentative
  dsimp only
  filter_upwards [F.euclideanMemLp.aestronglyMeasurable.ae_eq_mk] with x hx
  simpa only [HilbertVec.toVec_ofVec] using congrArg HilbertVec.toVec hx

private theorem cubeScaleFactor_div_pow_eq_sourceZPow_vectorP {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    cubeScaleFactor Q / (3 : ℝ) ^ j = (3 : ℝ) ^ (Q.scale - (j : ℤ)) := by
  unfold cubeScaleFactor
  rw [zpow_sub₀]
  · simp [div_eq_mul_inv]
  · norm_num

private theorem exactOverlapDepthWeight_rpow_eq_directWeight {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (j : ℕ) :
    (exactOverlapDepthWeight Q s.1 j) ^ p.exponent.toReal =
      ENNReal.ofReal
        (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) := by
  unfold exactOverlapDepthWeight exactOverlapSourceDepth
  rw [← ENNReal.rpow_mul]
  have hthree : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [hthree]
  rw [ENNReal.ofReal_rpow_of_pos (by norm_num : 0 < (3 : ℝ))]
  congr 1
  let r : ℝ := ((Q.scale - (j : ℤ) : ℤ) : ℝ)
  change ((3 : ℝ) ^ (-r * s.1 * p.exponent.toReal)) =
    Real.rpow 3 (-(s.1 * p.exponent.toReal * r))
  have hexp : -r * s.1 * p.exponent.toReal =
      -(s.1 * p.exponent.toReal * r) := by ring
  rw [hexp]
  rfl

/-- The direct vector overlap series before its outer finite-`p` root. -/
noncomputable def cubeEuclideanPositiveBesovOverlapPowerEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ := by
  classical
  exact ∑' j : ℕ,
    ENNReal.ofReal
        (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          (eLpNorm
            (fun x => HilbertVec.ofVec
              (F x - ScalarOverlap.cubeAverageVec S.1 F))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
              p.exponent.toReal)

/-- The canonical direct overlap seminorm to the exact finite `p` power is
its complete source scale series. -/
theorem cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^
        p.exponent.toReal =
      cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F := by
  rw [cubeEuclideanPositiveBesovOverlapESeminorm_eq]
  unfold cubeEuclideanPositiveBesovOverlapPowerEnergy
  rw [one_div]
  change ((∑' j : ℕ,
    ENNReal.ofReal
        (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          (eLpNorm
            (fun x => HilbertVec.ofVec
              (F x - ScalarOverlap.cubeAverageVec S.1 F))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
              p.exponent.toReal)) ^ (p.exponent.toReal)⁻¹) ^
      p.exponent.toReal = _
  exact ENNReal.rpow_inv_rpow (finiteLpExponent_toReal_pos p).ne' _

private theorem cubeAverageVec_congr_ae {d : ℕ} {Q : TriadicCube d}
    {F G : Vec d → Vec d} {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    ScalarOverlap.cubeAverageVec S F = ScalarOverlap.cubeAverageVec S G := by
  funext i
  apply Gagliardo.overlap_cubeAverage_congr_ae hS
  apply Gagliardo.ae_normalizedCubeMeasure_iff.mp
  filter_upwards [hFG] with x hx
  exact congrFun hx i

private theorem euclideanOverlapLocalENorm_congr_ae {d : ℕ} {Q : TriadicCube d}
    (p : FiniteLpExponent) {F G : Vec d → Vec d} {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    eLpNorm (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S) =
      eLpNorm (fun x => HilbertVec.ofVec (G x - ScalarOverlap.cubeAverageVec S G))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
  apply eLpNorm_congr_ae
  have hcube : F =ᵐ[cubeMeasure Q] G :=
    Gagliardo.ae_normalizedCubeMeasure_iff.mp hFG
  have hres : F =ᵐ[MeasureTheory.volume.restrict (ScalarOverlap.cubeSet S)] G := by
    have hsub : ScalarOverlap.cubeSet S ⊆ cubeSet Q :=
      ScalarOverlap.cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
    rw [cubeMeasure] at hcube
    exact ae_restrict_of_ae_restrict_of_subset hsub hcube
  have hlocal : F =ᵐ[ScalarOverlap.normalizedCubeMeasure S] G := by
    rw [ScalarOverlap.normalizedCubeMeasure, ScalarOverlap.cubeMeasure]
    exact Measure.ae_smul_measure hres _
  have havg := cubeAverageVec_congr_ae hS hFG
  filter_upwards [hlocal] with x hx
  rw [hx, havg]

/-- The direct canonical Euclidean overlap seminorm is invariant under an
almost-everywhere change on its parent cube. -/
theorem cubeEuclideanPositiveBesovOverlapESeminorm_congr_ae {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    {F G : Vec d → Vec d} (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p F =
      cubeEuclideanPositiveBesovOverlapESeminorm Q s p G := by
  rw [cubeEuclideanPositiveBesovOverlapESeminorm_eq,
    cubeEuclideanPositiveBesovOverlapESeminorm_eq]
  refine congrArg (· ^ (1 / p.exponent.toReal)) ?_
  refine tsum_congr fun j => ?_
  refine congrArg (HMul.hMul _) ?_
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [euclideanOverlapLocalENorm_congr_ae p S.2 hFG]

private theorem exactOverlapScalarPIntegrableOfEuclideanField {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p)
    (i : Fin d) : ExactOverlapIntegrable Q (fun x => F x i) where
  root := (cubeEuclideanLp_coordinate_memLp F i).integrable p.one_lt.le
  overlap := fun _ _ hS =>
    (Gagliardo.memLp_overlap_of_memLp (cubeEuclideanLp_coordinate_memLp F i) hS).integrable
      p.one_lt.le

/-- The finite sum of exact scalar overlap `p`-energies of the Euclidean
coordinates.  This is an internal aggregation device, not an additional
source-facing seminorm. -/
noncomputable def cubeEuclideanCoordinateExactOverlapPowerEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q p) : ℝ≥0∞ :=
  ∑ i : Fin d,
    (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
      (fun x => F x i) (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)) ^
        p.exponent.toReal

/-- The coordinate overlap series with the scale and center sums still
explicit. -/
noncomputable def cubeEuclideanCoordinateOverlapPowerEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q p) : ℝ≥0∞ := by
  classical
  exact ∑' j : ℕ,
    ENNReal.ofReal
        (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          ∑ i : Fin d,
            (eLpNorm
              (fun x => F x i - ScalarOverlap.cubeAverage S.1 (fun y => F y i))
              p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
                p.exponent.toReal)

private theorem exactScalarOverlapP_rpow_eq_coordinateSeries {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q p) (i : Fin d) :
    (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
      (fun x => F x i) (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)) ^
        p.exponent.toReal =
      ∑' j : ℕ,
        ENNReal.ofReal
            (Real.rpow 3
              (-(s.1 * p.exponent.toReal *
                (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
          ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
              (eLpNorm
                (fun x => F x i - ScalarOverlap.cubeAverage S.1 (fun y => F y i))
                p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
                  p.exponent.toReal) := by
  rw [exactOverlapScalarPSeminorm_rpow_eq_tsum_depthEnergy]
  apply tsum_congr
  intro j
  rw [exactOverlapDepthWeight_rpow_eq_directWeight]
  unfold exactOverlapDepthAverage
  have hsum :
      (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
        (exactOverlapLocalOscillation S.1 (ENNReal.ofReal p.exponent.toReal)
          (fun x => F x i)
          ((exactOverlapScalarPIntegrableOfEuclideanField Q p F i).overlap j S.1 S.2)) ^
            p.exponent.toReal) =
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          (eLpNorm
            (fun x => F x i - ScalarOverlap.cubeAverage S.1 (fun y => F y i))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
              p.exponent.toReal) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [exactOverlapLocalOscillation_eq]
        have hmean :
            exactOverlapLocalMean S.1 (fun x => F x i)
                ((exactOverlapScalarPIntegrableOfEuclideanField Q p F i).overlap j S.1 S.2) =
              ScalarOverlap.cubeAverage S.1 (fun x => F x i) := by
          rw [exactOverlapLocalMean_eq,
            ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]
        rw [hmean]
        congr
        exact ENNReal.ofReal_toReal p.lt_top.ne
  dsimp only
  rw [hsum]
  ring

/-- Reordering the nonnegative depth and coordinate sums identifies the
explicit coordinate series with the sum of exact scalar overlap energies. -/
theorem cubeEuclideanCoordinateOverlapPowerEnergy_eq_exact {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q p) :
    cubeEuclideanCoordinateOverlapPowerEnergy Q s p F =
      cubeEuclideanCoordinateExactOverlapPowerEnergy Q s p F := by
  unfold cubeEuclideanCoordinateOverlapPowerEnergy
    cubeEuclideanCoordinateExactOverlapPowerEnergy
  let w : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal
      (Real.rpow 3
        (-(s.1 * p.exponent.toReal *
          (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹
  let L : ℕ → TriadicCube d → Fin d → ℝ≥0∞ := fun j S i =>
    (eLpNorm
      (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
      p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal
  have hswap : ∀ j : ℕ,
      w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => ∑ i, L j S.1 i) =
        ∑ i : Fin d, w j *
          (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => L j S.1 i) := by
    intro j
    rw [Finset.sum_comm]
    rw [← Finset.mul_sum]
  change (∑' j : ℕ,
      w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => ∑ i, L j S.1 i)) = _
  calc
    (∑' j : ℕ,
        w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => ∑ i, L j S.1 i)) =
      ∑' j : ℕ, ∑ i : Fin d, w j *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => L j S.1 i) := by
        apply tsum_congr
        exact hswap
    _ = ∑' j : ℕ, ∑' i : Fin d, w j *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => L j S.1 i) := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
    _ = ∑' i : Fin d, ∑' j : ℕ, w j *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => L j S.1 i) :=
      ENNReal.tsum_comm
    _ = ∑ i : Fin d, ∑' j : ℕ, w j *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => L j S.1 i) := by
      rw [tsum_fintype]
    _ = ∑ i : Fin d,
        (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)) ^
            p.exponent.toReal := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      exact exactScalarOverlapP_rpow_eq_coordinateSeries Q s p F i

private theorem coordinate_overlap_local_power_le_dimension_mul_vector
    {d : ℕ} (S : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) :
    (∑ i : Fin d,
      (eLpNorm
        (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal) ≤
      (d : ℝ≥0∞) *
        (eLpNorm
          (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal := by
  calc
    (∑ i : Fin d,
        (eLpNorm
          (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal) =
      ∑ i : Fin d,
        (eLpNorm (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i)
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← scalarOverlap_eLpNorm_eq_coordinate_euclideanOverlapResidual]
    _ ≤ (d : ℝ≥0∞) *
        (eLpNorm
          (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal :=
      sum_coordinate_eLpNorm_rpow_le_dimension_mul
        (ScalarOverlap.normalizedCubeMeasure S) p
        (fun x => F x - ScalarOverlap.cubeAverageVec S F)

private theorem vector_overlap_local_power_le_coordinate_mul
    {d : ℕ} (S : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (hF : Measurable F) :
    (eLpNorm
      (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
      p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal ≤
      cubeCoordinateGagliardoComparisonConstant d p *
        ∑ i : Fin d,
          (eLpNorm
            (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal := by
  have hcoord : ∀ i : Fin d,
      AEStronglyMeasurable
        (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i)
        (ScalarOverlap.normalizedCubeMeasure S) := by
    intro i
    exact (((measurable_pi_apply i).comp hF).sub measurable_const).aestronglyMeasurable
  have hvector := euclidean_eLpNorm_rpow_le_dimension_rpow_mul_sum_rpow
    (ScalarOverlap.normalizedCubeMeasure S) p
    (fun x => F x - ScalarOverlap.cubeAverageVec S F) hcoord
  have hpower := finiteLpExponent_rpow_sum_le_card_rpow_mul_sum_rpow
    (fun i : Fin d =>
      eLpNorm (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i)
        p.exponent (ScalarOverlap.normalizedCubeMeasure S)) p
  calc
    (eLpNorm
      (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
      p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal ≤
      ‖(d : ℝ)‖ₑ ^ p.exponent.toReal *
        (∑ i : Fin d,
          eLpNorm (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i)
            p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal :=
      hvector
    _ ≤ ‖(d : ℝ)‖ₑ ^ p.exponent.toReal *
        ((d : ℝ≥0∞) ^ (p.exponent.toReal - 1) *
          ∑ i : Fin d,
            (eLpNorm (fun x => (F x - ScalarOverlap.cubeAverageVec S F) i)
              p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal) := by
      exact mul_le_mul_right (by simpa only [Fintype.card_fin] using hpower) _
    _ = cubeCoordinateGagliardoComparisonConstant d p *
        ∑ i : Fin d,
          (eLpNorm
            (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal := by
      rw [cubeCoordinateGagliardoComparisonConstant]
      rw [mul_assoc]
      congr 1

/-- Aggregating the coordinate lower bound over centers and all scales. -/
theorem cubeEuclideanCoordinateOverlapPowerEnergy_le_dimension_mul_overlap
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q p) :
    cubeEuclideanCoordinateOverlapPowerEnergy Q s p F ≤
      (d : ℝ≥0∞) * cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F := by
  let w : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal
      (Real.rpow 3
        (-(s.1 * p.exponent.toReal *
          (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹
  let C : ℕ → TriadicCube d → ℝ≥0∞ := fun j S =>
    ∑ i : Fin d,
      (eLpNorm
        (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal
  let V : ℕ → TriadicCube d → ℝ≥0∞ := fun _ S =>
    (eLpNorm
      (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
      p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal
  have hcenter : ∀ j : ℕ,
      (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1) ≤
        (d : ℝ≥0∞) *
          (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1) := by
    intro j
    calc
      (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1) ≤
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          (d : ℝ≥0∞) * V j S.1) := by
        apply Finset.sum_le_sum
        intro S _
        exact coordinate_overlap_local_power_le_dimension_mul_vector S.1 p F
      _ = (d : ℝ≥0∞) *
          (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1) := by
        rw [← Finset.mul_sum]
  change (∑' j : ℕ,
      w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1)) ≤
        (d : ℝ≥0∞) * ∑' j : ℕ,
          w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1)
  calc
    (∑' j : ℕ,
        w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1)) ≤
      ∑' j : ℕ, (d : ℝ≥0∞) *
        (w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1)) := by
        apply ENNReal.tsum_le_tsum
        intro j
        calc
          w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1) ≤
            w j * ((d : ℝ≥0∞) *
              (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1)) :=
            mul_le_mul_right (hcenter j) _
          _ = (d : ℝ≥0∞) *
              (w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1)) := by
            ring
    _ = (d : ℝ≥0∞) * ∑' j : ℕ,
        w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1) :=
      ENNReal.tsum_mul_left

/-- One scalar exact-overlap seminorm is controlled by the direct Euclidean
overlap seminorm.  This is the coordinate extraction needed when a scalar
positive test is assembled from a Euclidean fractional-Sobolev field. -/
theorem exactOverlapScalarPSeminorm_le_dimension_mul_cubeEuclideanOverlap
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) (i : Fin d)
    (hF : ExactOverlapIntegrable Q (fun x => F x i)) :
    exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
        (fun x => F x i) hF ≤
      (d : ℝ≥0∞) * cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
  let hcanonical := exactOverlapScalarPIntegrableOfEuclideanField Q p F i
  have hcongr :
      exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) hF =
        exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) hcanonical := by
    apply exactOverlapFiniteSeminorm_congr_ae
    intro _ _ _
    exact Filter.Eventually.of_forall fun _ => rfl
  have hterm :
      (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) hcanonical) ^ p.exponent.toReal ≤
        cubeEuclideanCoordinateExactOverlapPowerEnergy Q s p F := by
    unfold cubeEuclideanCoordinateExactOverlapPowerEnergy
    exact Finset.single_le_sum
      (fun k _ => (zero_le : (0 : ℝ≥0∞) ≤
        ((exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x k)
          (exactOverlapScalarPIntegrableOfEuclideanField Q p F k)) ^
            p.exponent.toReal)))
      (Finset.mem_univ i)
  have hpower :
      (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) hcanonical) ^ p.exponent.toReal ≤
        (d : ℝ≥0∞) *
          (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^
            p.exponent.toReal := by
    calc
      (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) hcanonical) ^ p.exponent.toReal ≤
        cubeEuclideanCoordinateExactOverlapPowerEnergy Q s p F := hterm
      _ = cubeEuclideanCoordinateOverlapPowerEnergy Q s p F := by
        rw [cubeEuclideanCoordinateOverlapPowerEnergy_eq_exact]
      _ ≤ (d : ℝ≥0∞) *
          (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^
            p.exponent.toReal := by
        rw [cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy]
        exact cubeEuclideanCoordinateOverlapPowerEnergy_le_dimension_mul_overlap
          Q s p F
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hroot := ENNReal.rpow_le_rpow hpower (inv_nonneg.mpr hp.le)
  have hd : 1 ≤ (d : ℝ≥0∞) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hinv : (p.exponent.toReal)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal (by norm_num) p.lt_top.ne).mpr p.one_lt.le
  have hdimension : (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ ≤ (d : ℝ≥0∞) := by
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow_of_exponent_le hd hinv
  rw [← hcongr]
  calc
    exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
        (fun x => F x i) hF =
      (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) hcanonical) ^
        (p.exponent.toReal * (p.exponent.toReal)⁻¹) := by
        rw [mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
    _ = ((exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) hcanonical) ^ p.exponent.toReal) ^
        (p.exponent.toReal)⁻¹ := by
        rw [ENNReal.rpow_mul]
    _ ≤ ((d : ℝ≥0∞) *
        (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^
          p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ := hroot
    _ = (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le),
          ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ (d : ℝ≥0∞) * cubeEuclideanPositiveBesovOverlapESeminorm Q s p F :=
      by simpa [mul_comm] using
        mul_le_mul_right hdimension
          (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F)

/-- Aggregating the finite-dimensional Euclidean upper bound over centers
and all scales.  Measurability is needed only to invoke the standard
coordinate-sum `L^p` estimate; it is not an additional regularity premise. -/
theorem cubeEuclideanOverlapPowerEnergy_le_coordinate_mul
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q p) (hF : Measurable F) :
    cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F ≤
      cubeCoordinateGagliardoComparisonConstant d p *
        cubeEuclideanCoordinateOverlapPowerEnergy Q s p F := by
  let w : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal
      (Real.rpow 3
        (-(s.1 * p.exponent.toReal *
          (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹
  let C : ℕ → TriadicCube d → ℝ≥0∞ := fun j S =>
    ∑ i : Fin d,
      (eLpNorm
        (fun x => F x i - ScalarOverlap.cubeAverage S (fun y => F y i))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal
  let V : ℕ → TriadicCube d → ℝ≥0∞ := fun _ S =>
    (eLpNorm
      (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
      p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ p.exponent.toReal
  let K := cubeCoordinateGagliardoComparisonConstant d p
  have hcenter : ∀ j : ℕ,
      (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1) ≤
        K * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1) := by
    intro j
    calc
      (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1) ≤
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => K * C j S.1) := by
        apply Finset.sum_le_sum
        intro S _
        exact vector_overlap_local_power_le_coordinate_mul S.1 p F hF
      _ = K * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1) := by
        rw [← Finset.mul_sum]
  change (∑' j : ℕ,
      w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1)) ≤
        K * ∑' j : ℕ,
          w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1)
  calc
    (∑' j : ℕ,
        w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1)) ≤
      ∑' j : ℕ, K *
        (w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1)) := by
        apply ENNReal.tsum_le_tsum
        intro j
        calc
          w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => V j S.1) ≤
            w j * (K *
              (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1)) :=
            mul_le_mul_right (hcenter j) _
          _ = K *
              (w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1)) := by
            ring
    _ = K * ∑' j : ℕ,
        w j * (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => C j S.1) :=
      ENNReal.tsum_mul_left

private theorem coordinate_exactOverlapPowerEnergy_le_overlapBesov_mul_gagliardo
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) (hF : Measurable F) :
    cubeEuclideanCoordinateExactOverlapPowerEnergy Q s p F ≤
      (2 * 3 ^ d) * cubeCoordinateGagliardoPowerEnergy Q s p F := by
  unfold cubeEuclideanCoordinateExactOverlapPowerEnergy
  calc
    (∑ i : Fin d,
        (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)) ^
            p.exponent.toReal) ≤
      ∑ i : Fin d, (2 * 3 ^ d) *
        (Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent (fun x => F x i)) ^
          p.exponent.toReal := by
        apply Finset.sum_le_sum
        intro i _
        exact exactOverlapScalarPSeminorm_rpow_le_gagliardo s p Q (fun x => F x i)
          (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)
          ((measurable_pi_apply i).comp hF)
          (cubeEuclideanLp_coordinate_memLp F i)
    _ = (2 * 3 ^ d) * cubeCoordinateGagliardoPowerEnergy Q s p F := by
      rw [cubeCoordinateGagliardoPowerEnergy, ← Finset.mul_sum]

private theorem coordinate_gagliardoPowerEnergy_le_lower_mul_exactOverlap
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) (hF : Measurable F) :
    cubeCoordinateGagliardoPowerEnergy Q s p F ≤
      (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal *
        cubeEuclideanCoordinateExactOverlapPowerEnergy Q s p F := by
  unfold cubeCoordinateGagliardoPowerEnergy
    cubeEuclideanCoordinateExactOverlapPowerEnergy
  calc
    (∑ i : Fin d,
        (Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent (fun x => F x i)) ^
          p.exponent.toReal) ≤
      ∑ i : Fin d, (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal *
        (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
          (fun x => F x i) (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)) ^
            p.exponent.toReal := by
        apply Finset.sum_le_sum
        intro i _
        exact gagliardo_rpow_le_exactOverlapScalarPSeminorm s p Q (fun x => F x i)
          (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)
          ((measurable_pi_apply i).comp hF)
          (cubeEuclideanLp_coordinate_memLp F i)
    _ = (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal *
        ∑ i : Fin d,
          (exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q
            (fun x => F x i) (exactOverlapScalarPIntegrableOfEuclideanField Q p F i)) ^
              p.exponent.toReal := by
      rw [← Finset.mul_sum]

noncomputable def cubeEuclideanOverlapToWspPowerConstant
    (d : ℕ) (p : FiniteLpExponent) : ℝ≥0∞ :=
  cubeCoordinateGagliardoComparisonConstant d p * (2 * 3 ^ d) *
    (d : ℝ≥0∞) * cubeEuclideanWspMetricComparisonConstant d p

noncomputable def cubeEuclideanWspToOverlapPowerConstant
    (d : ℕ) (p : FiniteLpExponent) : ℝ≥0∞ :=
  cubeCoordinateGagliardoComparisonConstant d p *
    (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal * (d : ℝ≥0∞)

theorem cubeEuclideanOverlapToWspPowerConstant_lt_top
    (d : ℕ) (p : FiniteLpExponent) :
    cubeEuclideanOverlapToWspPowerConstant d p < ∞ := by
  unfold cubeEuclideanOverlapToWspPowerConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (cubeCoordinateGagliardoComparisonConstant_lt_top d p)
        (by finiteness))
      (by finiteness))
    (cubeEuclideanWspMetricComparisonConstant_lt_top d p)

theorem cubeEuclideanWspToOverlapPowerConstant_lt_top
    (d : ℕ) (p : FiniteLpExponent) :
    cubeEuclideanWspToOverlapPowerConstant d p < ∞ := by
  unfold cubeEuclideanWspToOverlapPowerConstant
  have hlower : Gagliardo.gagliardoBesovLowerConstant d ≠ ∞ := by
    unfold Gagliardo.gagliardoBesovLowerConstant
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (ENNReal.pow_ne_top (by norm_num))
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top
      (cubeCoordinateGagliardoComparisonConstant_lt_top d p)
      (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hlower))
    (by finiteness)

/-- The canonical direct Euclidean overlap seminorm controls the Euclidean
fractional Sobolev seminorm at the same finite exponent.  The only explicit
representative premise supplies the scalar measurability required by the
already-established scalar Gagliardo comparison. -/
private theorem cubeEuclideanOverlap_rpow_le_constant_mul_wsp_of_measurable
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) (hF : Measurable F) :
    (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^ p.exponent.toReal ≤
      cubeEuclideanOverlapToWspPowerConstant d p *
        (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal := by
  let A := cubeCoordinateGagliardoComparisonConstant d p
  let B : ℝ≥0∞ := 2 * 3 ^ d
  let M := cubeEuclideanWspMetricComparisonConstant d p
  calc
    (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^ p.exponent.toReal =
        cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F :=
      cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy Q s p F
    _ ≤ A * cubeEuclideanCoordinateOverlapPowerEnergy Q s p F :=
      cubeEuclideanOverlapPowerEnergy_le_coordinate_mul Q s p F hF
    _ = A * cubeEuclideanCoordinateExactOverlapPowerEnergy Q s p F := by
      rw [cubeEuclideanCoordinateOverlapPowerEnergy_eq_exact]
    _ ≤ A * (B * cubeCoordinateGagliardoPowerEnergy Q s p F) := by
      exact mul_le_mul_right
        (coordinate_exactOverlapPowerEnergy_le_overlapBesov_mul_gagliardo Q s p F hF) A
    _ ≤ A * (B * ((d : ℝ≥0∞) *
        (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal)) := by
      gcongr
      exact cubeCoordinateGagliardoPowerEnergy_le_dimension_mul_ambientHilbert Q s p F
    _ ≤ A * (B * ((d : ℝ≥0∞) * (M *
        (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal))) := by
      gcongr
      exact cubeAmbientHilbertWspESeminorm_rpow_le_metricComparisonConstant_mul Q s p F
    _ = cubeEuclideanOverlapToWspPowerConstant d p *
        (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal := by
      unfold cubeEuclideanOverlapToWspPowerConstant
      dsimp [A, B, M]
      ring

/-- The Euclidean fractional Sobolev seminorm controls the canonical direct
Euclidean overlap seminorm at the same finite exponent. -/
private theorem cubeEuclideanWsp_rpow_le_constant_mul_overlap_of_measurable
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) (hF : Measurable F) :
    (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal ≤
      cubeEuclideanWspToOverlapPowerConstant d p *
        (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^ p.exponent.toReal := by
  let A := cubeCoordinateGagliardoComparisonConstant d p
  let L := (Gagliardo.gagliardoBesovLowerConstant d) ^ p.exponent.toReal
  calc
    (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal ≤
      (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal :=
      cubeEuclideanWspESeminorm_rpow_le_ambientHilbert Q s p F
    _ ≤ A * cubeCoordinateGagliardoPowerEnergy Q s p F :=
      cubeAmbientHilbertWspESeminorm_rpow_le_coordinateGagliardoPowerEnergy Q s p F hF
    _ ≤ A * (L * cubeEuclideanCoordinateExactOverlapPowerEnergy Q s p F) := by
      exact mul_le_mul_right
        (coordinate_gagliardoPowerEnergy_le_lower_mul_exactOverlap Q s p F hF) A
    _ ≤ A * (L * ((d : ℝ≥0∞) *
        cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F)) := by
      gcongr
      rw [← cubeEuclideanCoordinateOverlapPowerEnergy_eq_exact]
      exact cubeEuclideanCoordinateOverlapPowerEnergy_le_dimension_mul_overlap Q s p F
    _ = cubeEuclideanWspToOverlapPowerConstant d p *
        (cubeEuclideanPositiveBesovOverlapESeminorm Q s p F) ^ p.exponent.toReal := by
      rw [cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy]
      unfold cubeEuclideanWspToOverlapPowerConstant
      dsimp [A, L]
      ring

private theorem finiteLpExponent_toReal_inv_pos (p : FiniteLpExponent) :
    0 < (p.exponent.toReal)⁻¹ :=
  inv_pos.mpr (finiteLpExponent_toReal_pos p)

/-- A deliberately coarse constant depending only on the dimension.  It
absorbs the finite-coordinate and metric changes without any dependence on
the fractional order or the finite exponent. -/
noncomputable def cubeEuclideanWspOverlapDimensionConstant (d : ℕ) : ℝ≥0∞ :=
  (2 * 3 ^ d) * Gagliardo.gagliardoBesovLowerConstant d *
    (d : ℝ≥0∞) ^ ((d : ℝ) + 4)

/-- The dimension-only overlap/fractional comparison constant is finite. -/
theorem cubeEuclideanWspOverlapDimensionConstant_lt_top (d : ℕ) :
    cubeEuclideanWspOverlapDimensionConstant d < ∞ := by
  unfold cubeEuclideanWspOverlapDimensionConstant
  have hlower : Gagliardo.gagliardoBesovLowerConstant d ≠ ∞ := by
    unfold Gagliardo.gagliardoBesovLowerConstant
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (ENNReal.pow_ne_top (by norm_num))
  have hdimension : 0 ≤ (d : ℝ) + 4 := by positivity
  have hpower : (d : ℝ≥0∞) ^ ((d : ℝ) + 4) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg hdimension (ENNReal.natCast_ne_top d)
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by finiteness) (lt_top_iff_ne_top.mpr hlower)) hpower

private theorem ennreal_natCast_one_le {d : ℕ} [NeZero d] :
    1 ≤ (d : ℝ≥0∞) := by
  exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (NeZero.ne d))

private theorem finiteLpExponent_toReal_one_le (p : FiniteLpExponent) :
    1 ≤ p.exponent.toReal := by
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal (by norm_num) p.lt_top.ne).mpr p.one_lt.le

private theorem finiteLpExponent_inv_le_one (p : FiniteLpExponent) :
    (p.exponent.toReal)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (finiteLpExponent_toReal_one_le p)

private theorem finiteLpExponent_sub_mul_inv_le_one (p : FiniteLpExponent) :
    (p.exponent.toReal - 1) * (p.exponent.toReal)⁻¹ ≤ 1 := by
  have hp : p.exponent.toReal ≠ 0 := (finiteLpExponent_toReal_pos p).ne'
  rw [sub_mul, mul_inv_cancel₀ hp, one_mul]
  linarith [(inv_nonneg).mpr (finiteLpExponent_toReal_pos p).le]

private theorem finiteLpExponent_dimension_add_mul_inv_le_dimension_add_one
    (d : ℕ) (p : FiniteLpExponent) :
    ((d : ℝ) + p.exponent.toReal) * (p.exponent.toReal)⁻¹ ≤ (d : ℝ) + 1 := by
  have hinv : (p.exponent.toReal)⁻¹ ≤ 1 := finiteLpExponent_inv_le_one p
  have hcancel : p.exponent.toReal * (p.exponent.toReal)⁻¹ = 1 :=
    mul_inv_cancel₀ (finiteLpExponent_toReal_pos p).ne'
  rw [add_mul, hcancel]
  calc
    (d : ℝ) * (p.exponent.toReal)⁻¹ + 1 ≤ (d : ℝ) * 1 + 1 :=
      by
        simpa [add_comm] using (add_le_add_right
          (mul_le_mul_of_nonneg_left hinv (show 0 ≤ (d : ℝ) by positivity)) 1)
    _ = (d : ℝ) + 1 := by ring

private theorem cubeCoordinateComparisonConstant_root_le_dimension_sq
    {d : ℕ} [NeZero d] (p : FiniteLpExponent) :
    (cubeCoordinateGagliardoComparisonConstant d p) ^ (p.exponent.toReal)⁻¹ ≤
      (d : ℝ≥0∞) ^ (2 : ℝ) := by
  unfold cubeCoordinateGagliardoComparisonConstant
  rw [ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le,
    ENNReal.rpow_rpow_inv (finiteLpExponent_toReal_pos p).ne',
    ← ENNReal.rpow_mul]
  have hd : 1 ≤ (d : ℝ≥0∞) := ennreal_natCast_one_le
  have hpow : (d : ℝ≥0∞) ^
      ((p.exponent.toReal - 1) * (p.exponent.toReal)⁻¹) ≤ (d : ℝ≥0∞) := by
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le hd
      (finiteLpExponent_sub_mul_inv_le_one p)
  have hnorm : ‖(d : ℝ)‖ₑ = (d : ℝ≥0∞) := by simp
  rw [hnorm]
  calc
    (d : ℝ≥0∞) * (d : ℝ≥0∞) ^
        ((p.exponent.toReal - 1) * (p.exponent.toReal)⁻¹) ≤
      (d : ℝ≥0∞) * (d : ℝ≥0∞) := mul_le_mul_right hpow _
    _ = (d : ℝ≥0∞) ^ (2 : ℝ) := by simp [pow_two]

private theorem cubeMetricComparisonConstant_root_le_dimension_power
    {d : ℕ} [NeZero d] (p : FiniteLpExponent) :
    (cubeEuclideanWspMetricComparisonConstant d p) ^ (p.exponent.toReal)⁻¹ ≤
      (d : ℝ≥0∞) ^ ((d : ℝ) + 1) := by
  unfold cubeEuclideanWspMetricComparisonConstant
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [← ENNReal.ofReal_rpow_of_pos hdreal, ← ENNReal.rpow_mul]
  have hd : 1 ≤ (d : ℝ≥0∞) := ennreal_natCast_one_le
  convert ENNReal.rpow_le_rpow_of_exponent_le hd
    (finiteLpExponent_dimension_add_mul_inv_le_dimension_add_one d p) using 1
  all_goals simp

private theorem flatOverlapConstant_root_le_flatOverlapConstant
    (d : ℕ) (p : FiniteLpExponent) :
    (2 * 3 ^ d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ ≤ 2 * 3 ^ d := by
  have hbase : 1 ≤ (2 * 3 ^ d : ℝ≥0∞) := by
    calc
      (1 : ℝ≥0∞) ≤ 2 := by norm_num
      _ = 2 * 1 := by norm_num
      _ ≤ 2 * 3 ^ d := mul_le_mul_right
        (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 3)) _
  simpa only [ENNReal.rpow_one] using
    ENNReal.rpow_le_rpow_of_exponent_le hbase (finiteLpExponent_inv_le_one p)

private theorem gagliardoBesovLowerConstant_one_le (d : ℕ) :
    1 ≤ Gagliardo.gagliardoBesovLowerConstant d := by
  unfold Gagliardo.gagliardoBesovLowerConstant
  calc
    (1 : ℝ≥0∞) ≤ 2 ^ 3 := by norm_num
    _ = 2 ^ 3 * 1 := by ring
    _ ≤ 2 ^ 3 * 3 ^ (3 * d + 2) :=
      mul_le_mul_right (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 3)) _

private theorem dimension_power_three_le_dimension_power_large {d : ℕ} [NeZero d] :
    (d : ℝ≥0∞) ^ (3 : ℝ) ≤ (d : ℝ≥0∞) ^ ((d : ℝ) + 2) := by
  apply ENNReal.rpow_le_rpow_of_exponent_le ennreal_natCast_one_le
  have hd : 1 ≤ (d : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  linarith

private theorem dimension_square_mul_metric_le_large {d : ℕ} [NeZero d] :
    (d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) *
      (d : ℝ≥0∞) ^ ((d : ℝ) + 1) ≤ (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
  have hD : 1 ≤ (d : ℝ≥0∞) := ennreal_natCast_one_le
  have hzero : (d : ℝ≥0∞) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hD)
  have htop : (d : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top d
  have hfirst : (d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) ≤
      (d : ℝ≥0∞) ^ (3 : ℝ) := by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num,
      show (3 : ℝ) = (3 : ℕ) by norm_num,
      ENNReal.rpow_natCast, ENNReal.rpow_natCast]
    simp [pow_succ]
  have hsecond : (d : ℝ≥0∞) ^ (3 : ℝ) *
      (d : ℝ≥0∞) ^ ((d : ℝ) + 1) ≤ (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
    -- The direct exponent combination is more convenient than reusing the
    -- coarse intermediate bound.
    rw [← ENNReal.rpow_add _ _ hzero htop]
    apply ENNReal.rpow_le_rpow_of_exponent_le hD
    linarith
  calc
    (d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) *
        (d : ℝ≥0∞) ^ ((d : ℝ) + 1) =
      ((d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞)) *
        (d : ℝ≥0∞) ^ ((d : ℝ) + 1) := by ring
    _ ≤ (d : ℝ≥0∞) ^ (3 : ℝ) *
        (d : ℝ≥0∞) ^ ((d : ℝ) + 1) := by
      simpa [mul_comm] using mul_le_mul_right hfirst
        ((d : ℝ≥0∞) ^ ((d : ℝ) + 1))
    _ ≤ _ := hsecond

theorem cubeEuclideanOverlapRootConstant_le_dimensionConstant
    {d : ℕ} [NeZero d] (p : FiniteLpExponent) :
    (cubeEuclideanOverlapToWspPowerConstant d p) ^ (p.exponent.toReal)⁻¹ ≤
      cubeEuclideanWspOverlapDimensionConstant d := by
  have hA := cubeCoordinateComparisonConstant_root_le_dimension_sq (d := d) p
  have hB := flatOverlapConstant_root_le_flatOverlapConstant d p
  have hD : (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ ≤ (d : ℝ≥0∞) := by
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow_of_exponent_le ennreal_natCast_one_le
        (finiteLpExponent_inv_le_one p)
  have hM := cubeMetricComparisonConstant_root_le_dimension_power (d := d) p
  unfold cubeEuclideanOverlapToWspPowerConstant
    cubeEuclideanWspOverlapDimensionConstant
  rw [ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le,
    ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le,
    ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le]
  calc
    cubeCoordinateGagliardoComparisonConstant d p ^ (p.exponent.toReal)⁻¹ *
        (2 * 3 ^ d) ^ (p.exponent.toReal)⁻¹ *
          (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ *
            cubeEuclideanWspMetricComparisonConstant d p ^ (p.exponent.toReal)⁻¹ ≤
      (d : ℝ≥0∞) ^ (2 : ℝ) *
        (2 * 3 ^ d) ^ (p.exponent.toReal)⁻¹ *
          (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ *
            cubeEuclideanWspMetricComparisonConstant d p ^ (p.exponent.toReal)⁻¹ := by
      gcongr
    _ ≤ (d : ℝ≥0∞) ^ (2 : ℝ) * (2 * 3 ^ d) *
          (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ *
            cubeEuclideanWspMetricComparisonConstant d p ^ (p.exponent.toReal)⁻¹ := by
      gcongr
    _ ≤ (d : ℝ≥0∞) ^ (2 : ℝ) * (2 * 3 ^ d) * (d : ℝ≥0∞) *
            cubeEuclideanWspMetricComparisonConstant d p ^ (p.exponent.toReal)⁻¹ := by
      gcongr
    _ ≤ (d : ℝ≥0∞) ^ (2 : ℝ) * (2 * 3 ^ d) * (d : ℝ≥0∞) *
            (d : ℝ≥0∞) ^ ((d : ℝ) + 1) := by
      gcongr
    _ ≤ (2 * 3 ^ d) * (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
      rw [show (d : ℝ≥0∞) ^ (2 : ℝ) * (2 * 3 ^ d) * (d : ℝ≥0∞) *
          (d : ℝ≥0∞) ^ ((d : ℝ) + 1) =
        (2 * 3 ^ d) * ((d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) *
          (d : ℝ≥0∞) ^ ((d : ℝ) + 1)) by ring]
      exact mul_le_mul_right (dimension_square_mul_metric_le_large (d := d)) _
    _ ≤ (2 * 3 ^ d) * Gagliardo.gagliardoBesovLowerConstant d *
        (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
      calc
        (2 * 3 ^ d) * (d : ℝ≥0∞) ^ ((d : ℝ) + 4) =
          ((2 * 3 ^ d) * 1) * (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by ring
        _ ≤ ((2 * 3 ^ d) * Gagliardo.gagliardoBesovLowerConstant d) *
            (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
          gcongr
          exact gagliardoBesovLowerConstant_one_le d
        _ = _ := by ring

theorem cubeEuclideanWspRootConstant_le_dimensionConstant
    {d : ℕ} [NeZero d] (p : FiniteLpExponent) :
    (cubeEuclideanWspToOverlapPowerConstant d p) ^ (p.exponent.toReal)⁻¹ ≤
      cubeEuclideanWspOverlapDimensionConstant d := by
  have hA := cubeCoordinateComparisonConstant_root_le_dimension_sq (d := d) p
  have hD : (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ ≤ (d : ℝ≥0∞) := by
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow_of_exponent_le ennreal_natCast_one_le
        (finiteLpExponent_inv_le_one p)
  unfold cubeEuclideanWspToOverlapPowerConstant
    cubeEuclideanWspOverlapDimensionConstant
  rw [ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le,
    ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le,
    ENNReal.rpow_rpow_inv (finiteLpExponent_toReal_pos p).ne']
  calc
    cubeCoordinateGagliardoComparisonConstant d p ^ (p.exponent.toReal)⁻¹ *
        Gagliardo.gagliardoBesovLowerConstant d *
          (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ ≤
      (d : ℝ≥0∞) ^ (2 : ℝ) * Gagliardo.gagliardoBesovLowerConstant d *
          (d : ℝ≥0∞) ^ (p.exponent.toReal)⁻¹ := by
      gcongr
    _ ≤ (d : ℝ≥0∞) ^ (2 : ℝ) * Gagliardo.gagliardoBesovLowerConstant d *
          (d : ℝ≥0∞) := by
      gcongr
    _ ≤ (d : ℝ≥0∞) ^ (2 : ℝ) * Gagliardo.gagliardoBesovLowerConstant d *
          (d : ℝ≥0∞) ^ (3 : ℝ) := by
      have hDthree : (d : ℝ≥0∞) ≤ (d : ℝ≥0∞) ^ (3 : ℝ) := by
        calc
          (d : ℝ≥0∞) = (d : ℝ≥0∞) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
          _ ≤ (d : ℝ≥0∞) ^ (3 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (ennreal_natCast_one_le (d := d))
              (show (1 : ℝ) ≤ 3 by norm_num)
      gcongr
    _ ≤ (2 * 3 ^ d) * Gagliardo.gagliardoBesovLowerConstant d *
        (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
      have hthree := dimension_power_three_le_dimension_power_large (d := d)
      have hzero : (d : ℝ≥0∞) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le (by norm_num) (ennreal_natCast_one_le (d := d)))
      have htop : (d : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top d
      have hcombine : (d : ℝ≥0∞) ^ (2 : ℝ) *
          (d : ℝ≥0∞) ^ ((d : ℝ) + 2) =
            (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
        rw [← ENNReal.rpow_add _ _ hzero htop]
        congr 1
        ring
      calc
        (d : ℝ≥0∞) ^ (2 : ℝ) * Gagliardo.gagliardoBesovLowerConstant d *
            (d : ℝ≥0∞) ^ (3 : ℝ) =
          Gagliardo.gagliardoBesovLowerConstant d *
            ((d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) ^ (3 : ℝ)) := by ring
        _ ≤ Gagliardo.gagliardoBesovLowerConstant d *
            ((d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) ^ ((d : ℝ) + 2)) := by
          gcongr
        _ ≤ (2 * 3 ^ d) * Gagliardo.gagliardoBesovLowerConstant d *
            (d : ℝ≥0∞) ^ ((d : ℝ) + 4) := by
          have hflat : (1 : ℝ≥0∞) ≤ 2 * 3 ^ d := by
            calc
              (1 : ℝ≥0∞) ≤ 2 := by norm_num
              _ = 2 * 1 := by norm_num
              _ ≤ 2 * 3 ^ d := mul_le_mul_right
                (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 3)) _
          calc
            Gagliardo.gagliardoBesovLowerConstant d *
                ((d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) ^ ((d : ℝ) + 2)) ≤
              (2 * 3 ^ d) * (Gagliardo.gagliardoBesovLowerConstant d *
                ((d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) ^ ((d : ℝ) + 2))) := by
              simpa only [one_mul] using mul_le_mul_left hflat
                (Gagliardo.gagliardoBesovLowerConstant d *
                  ((d : ℝ≥0∞) ^ (2 : ℝ) * (d : ℝ≥0∞) ^ ((d : ℝ) + 2)))
            _ = _ := by rw [hcombine]; ring

/-- Rooted form of the direct-overlap-to-fractional-Sobolev comparison. -/
private theorem cubeEuclideanOverlap_le_rootConstant_mul_wsp_of_measurable
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) (hF : Measurable F) :
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p F ≤
      (cubeEuclideanOverlapToWspPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanWspESeminorm Q s p F := by
  have hpower := cubeEuclideanOverlap_rpow_le_constant_mul_wsp_of_measurable Q s p F hF
  have hroot := ENNReal.rpow_le_rpow hpower
    (finiteLpExponent_toReal_inv_pos p).le
  rw [← ENNReal.rpow_mul] at hroot
  have hprod : p.exponent.toReal * (p.exponent.toReal)⁻¹ = 1 := by
    exact mul_inv_cancel₀ (finiteLpExponent_toReal_pos p).ne'
  rw [hprod, ENNReal.rpow_one] at hroot
  rw [ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le,
    ENNReal.rpow_rpow_inv (finiteLpExponent_toReal_pos p).ne'] at hroot
  exact hroot

/-- Rooted form of the fractional-Sobolev-to-direct-overlap comparison. -/
private theorem cubeEuclideanWsp_le_rootConstant_mul_overlap_of_measurable
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) (hF : Measurable F) :
    cubeEuclideanWspESeminorm Q s p F ≤
      (cubeEuclideanWspToOverlapPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
  have hpower := cubeEuclideanWsp_rpow_le_constant_mul_overlap_of_measurable Q s p F hF
  have hroot := ENNReal.rpow_le_rpow hpower
    (finiteLpExponent_toReal_inv_pos p).le
  rw [← ENNReal.rpow_mul] at hroot
  have hprod : p.exponent.toReal * (p.exponent.toReal)⁻¹ = 1 := by
    exact mul_inv_cancel₀ (finiteLpExponent_toReal_pos p).ne'
  rw [hprod, ENNReal.rpow_one] at hroot
  rw [ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_inv_pos p).le,
    ENNReal.rpow_rpow_inv (finiteLpExponent_toReal_pos p).ne'] at hroot
  exact hroot

/-- Source-facing finite-`p` overlap-to-fractional comparison.  The field
carrier provides only its `L^p` class; a globally measurable representative
is selected internally and the two seminorms are transported back by their
proved a.e. congruence. -/
theorem cubeEuclideanOverlap_le_rootConstant_mul_wsp
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) :
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p F ≤
      (cubeEuclideanOverlapToWspPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanWspESeminorm Q s p F := by
  let G := F.measurableRepresentative
  have hFG : F =ᵐ[normalizedCubeMeasure Q] G := F.ae_eq_measurableRepresentative
  calc
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p F =
        cubeEuclideanPositiveBesovOverlapESeminorm Q s p G :=
      cubeEuclideanPositiveBesovOverlapESeminorm_congr_ae hFG
    _ ≤ (cubeEuclideanOverlapToWspPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanWspESeminorm Q s p G :=
      cubeEuclideanOverlap_le_rootConstant_mul_wsp_of_measurable Q s p G
        F.measurable_measurableRepresentative
    _ = (cubeEuclideanOverlapToWspPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanWspESeminorm Q s p F := by
      rw [cubeEuclideanWspESeminorm_congr_ae hFG]

/-- Source-facing finite-`p` fractional-to-overlap comparison, with the same
internally selected measurable representative. -/
theorem cubeEuclideanWsp_le_rootConstant_mul_overlap
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) :
    cubeEuclideanWspESeminorm Q s p F ≤
      (cubeEuclideanWspToOverlapPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
  let G := F.measurableRepresentative
  have hFG : F =ᵐ[normalizedCubeMeasure Q] G := F.ae_eq_measurableRepresentative
  calc
    cubeEuclideanWspESeminorm Q s p F = cubeEuclideanWspESeminorm Q s p G :=
      cubeEuclideanWspESeminorm_congr_ae hFG
    _ ≤ (cubeEuclideanWspToOverlapPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s p G :=
      cubeEuclideanWsp_le_rootConstant_mul_overlap_of_measurable Q s p G
        F.measurable_measurableRepresentative
    _ = (cubeEuclideanWspToOverlapPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
      rw [cubeEuclideanPositiveBesovOverlapESeminorm_congr_ae hFG]

/-- Source-facing finite-`p` overlap-to-fractional comparison with a constant
depending only on the dimension. -/
theorem cubeEuclideanOverlap_le_dimensionConstant_mul_wsp
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) :
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p F ≤
      cubeEuclideanWspOverlapDimensionConstant d *
        cubeEuclideanWspESeminorm Q s p F := by
  calc
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p F ≤
        (cubeEuclideanOverlapToWspPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
          cubeEuclideanWspESeminorm Q s p F :=
      cubeEuclideanOverlap_le_rootConstant_mul_wsp Q s p F
    _ ≤ cubeEuclideanWspOverlapDimensionConstant d *
          cubeEuclideanWspESeminorm Q s p F :=
      mul_le_mul_left (cubeEuclideanOverlapRootConstant_le_dimensionConstant p) _

/-- Source-facing finite-`p` fractional-to-overlap comparison with the same
dimension-only constant. -/
theorem cubeEuclideanWsp_le_dimensionConstant_mul_overlap
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q p) :
    cubeEuclideanWspESeminorm Q s p F ≤
      cubeEuclideanWspOverlapDimensionConstant d *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s p F := by
  calc
    cubeEuclideanWspESeminorm Q s p F ≤
        (cubeEuclideanWspToOverlapPowerConstant d p) ^ (p.exponent.toReal)⁻¹ *
          cubeEuclideanPositiveBesovOverlapESeminorm Q s p F :=
      cubeEuclideanWsp_le_rootConstant_mul_overlap Q s p F
    _ ≤ cubeEuclideanWspOverlapDimensionConstant d *
          cubeEuclideanPositiveBesovOverlapESeminorm Q s p F :=
      mul_le_mul_left (cubeEuclideanWspRootConstant_le_dimensionConstant p) _

end

end Homogenization
