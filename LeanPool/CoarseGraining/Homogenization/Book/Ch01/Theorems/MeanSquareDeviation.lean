/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Euclidean
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.Seminorms
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Mean Square Deviation -/

namespace Homogenization
namespace Book
namespace Ch01

/-!
# Mean-square deviation toolkit

Scalar and vector mean-square deviation of a field from a constant, together
with the companion mean-square oscillation, are the `L²`-normalized quantities
used to measure how far a field sits from its average on a domain.  This file
collects their basic identities: rewriting the vector deviation as a volume
average of the squared coordinate norm of the centered field (for square-
integrable fields), the explicit-Euclidean-ball finiteness facts they rely on,
and the norm-equivalence bound of the deviation from zero by the ambient `L²`
seminorm.
-/

open scoped BigOperators ENNReal

noncomputable section

/-- Mean square deviation of a scalar function from a constant on a set. -/
noncomputable def meanSquareDeviationOn {d : ℕ} (V : Set (Vec d))
    (u : Vec d → ℝ) (c : ℝ) : ℝ :=
  volumeAverage V fun y => (u y - c) ^ 2

/-- Real volume of the explicit unit Euclidean ball. -/
noncomputable def euclideanUnitBallVolume (d : ℕ) : ℝ :=
  (MeasureTheory.volume (euclideanBall (0 : Vec d) 1)).toReal

/-- Componentwise mean square deviation of a vector field from a constant. -/
noncomputable def meanSquareDeviationVecOn {d : ℕ} (V : Set (Vec d))
    (h : Vec d → Vec d) (c : Vec d) : ℝ :=
  ∑ k : Fin d, meanSquareDeviationOn V (fun y => h y k) (c k)

/-- Componentwise mean square oscillation of a vector field on a set. -/
noncomputable def meanSquareOscillationVecOn {d : ℕ} (V : Set (Vec d))
    (h : Vec d → Vec d) : ℝ :=
  meanSquareDeviationVecOn V h (volumeAverageVec V h)

/--
Vector mean-square deviation is the volume average of the squared coordinate
norm of the centered vector field, when the componentwise squares are
integrable.
-/
theorem meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub
    {d : ℕ} {V : Set (Vec d)} {h : Vec d → Vec d} {c : Vec d}
    (hint :
      ∀ k : Fin d, MeasureTheory.IntegrableOn (fun x => (h x k - c k) ^ 2) V) :
    meanSquareDeviationVecOn V h c =
      volumeAverage V (fun x => vecNormSq (h x - c)) := by
  unfold meanSquareDeviationVecOn meanSquareDeviationOn volumeAverage vecNormSq vecDot
  rw [← Finset.mul_sum]
  congr 1
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro k _hk
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp [pow_two]
  · intro k _hk
    simpa [pow_two] using (hint k).integrable

/--
For an `L²` vector field on a finite-measure set, every coordinate after
subtracting a constant has an integrable square.
-/
theorem integrableOn_coord_sub_const_sq_of_memVectorL2
    {d : ℕ} {V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {h : Vec d → Vec d} (hh : MemVectorL2 V h) (c : Vec d) (k : Fin d) :
    MeasureTheory.IntegrableOn (fun x => (h x k - c k) ^ 2) V := by
  have hhcomp : MemScalarL2 V (fun x => h x k) :=
    memScalarL2_coord_of_memVectorL2 hh k
  have hcvec : MemVectorL2 V (fun _ : Vec d => c) :=
    memVectorL2_const (U := V) c
  have hccomp : MemScalarL2 V (fun _ : Vec d => c k) :=
    memScalarL2_coord_of_memVectorL2 hcvec k
  have hdiff : MemScalarL2 V (fun x => h x k - c k) := hhcomp.sub hccomp
  simpa [pow_two, MemScalarL2, volumeMeasureOn, MeasureTheory.IntegrableOn] using!
    hdiff.integrable_mul hdiff

/--
Vector mean-square deviation is the volume average of the squared coordinate
norm of the centered vector field for every `L²` vector field on a
finite-measure set.
-/
theorem meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub_of_memVectorL2
    {d : ℕ} {V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {h : Vec d → Vec d} (hh : MemVectorL2 V h) (c : Vec d) :
    meanSquareDeviationVecOn V h c =
      volumeAverage V (fun x => vecNormSq (h x - c)) := by
  exact meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub
    (fun k => integrableOn_coord_sub_const_sq_of_memVectorL2 hh c k)

/-- Explicit Euclidean balls have finite volume. -/
theorem volume_euclideanBall_ne_top {d : ℕ} (x : Vec d) (r : ℝ) :
    MeasureTheory.volume (euclideanBall x r) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    ((isCompact_euclideanClosedBall x (abs_nonneg r)).measure_ne_top
      (μ := MeasureTheory.volume)) ?_
  exact MeasureTheory.measure_mono (euclideanBall_subset_euclideanClosedBall_abs x r)

/-- Positive-radius explicit Euclidean balls have nonzero real volume. -/
theorem volume_euclideanBall_toReal_ne_zero {d : ℕ} (x : Vec d) {r : ℝ} (hr : 0 < r) :
    (MeasureTheory.volume (euclideanBall x r)).toReal ≠ 0 := by
  rw [ENNReal.toReal_ne_zero]
  constructor
  · exact ne_of_gt
      ((isOpen_euclideanBall x r).measure_pos MeasureTheory.volume
        (euclideanBall_nonempty x hr))
  · exact volume_euclideanBall_ne_top x r

/-- The volume measure restricted to an explicit Euclidean ball is finite. -/
theorem isFiniteMeasure_volumeMeasureOn_euclideanBall {d : ℕ} (x : Vec d) (r : ℝ) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (euclideanBall x r)) := by
  simpa [volumeMeasureOn] using
    (MeasureTheory.isFiniteMeasure_restrict.mpr
      (volume_euclideanBall_ne_top x r))

/--
Mean-square deviation from zero is controlled by the square of the ambient
`L²` seminorm, with the expected finite-dimensional norm-equivalence factor.
-/
theorem meanSquareDeviationVecOn_zero_le_card_mul_volume_inv_mul_eLpNorm_sq
    {d : ℕ} {V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {F : Vec d → Vec d}
    (hvol : 0 < (MeasureTheory.volume V).toReal)
    (hF : MemVectorL2 V F) :
    meanSquareDeviationVecOn V F 0 ≤
      (Fintype.card (Fin d) : ℝ) * ((MeasureTheory.volume V).toReal)⁻¹ *
        (MeasureTheory.eLpNorm F (2 : ℝ≥0∞) (volumeMeasureOn V)).toReal ^ 2 := by
  let card : ℝ := Fintype.card (Fin d)
  have hdev :
      meanSquareDeviationVecOn V F 0 =
        volumeAverage V (fun x => vecNormSq (F x)) := by
    simpa using
      meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub_of_memVectorL2
        (V := V) (h := F) hF (0 : Vec d)
  have hvec_int :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (F x)) V MeasureTheory.volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF hF
  have hnorm_int :
      MeasureTheory.IntegrableOn (fun x => ‖F x‖ ^ (2 : ℕ)) V MeasureTheory.volume := by
    have h :=
      hF.integrable_norm_rpow
        (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, Real.rpow_two] using h
  have hint_le :
      ∫ x in V, vecNormSq (F x) ∂MeasureTheory.volume ≤
        ∫ x in V, card * ‖F x‖ ^ (2 : ℕ) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_mono_ae hvec_int (hnorm_int.const_mul card) ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [card] using Homogenization.vecNormSq_le_card_mul_norm_sq (F x)
  have hconst_mul :
      ∫ x in V, card * ‖F x‖ ^ (2 : ℕ) ∂MeasureTheory.volume =
        card * ∫ x in V, ‖F x‖ ^ (2 : ℕ) ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  have hlp_sq :
      (MeasureTheory.eLpNorm F (2 : ℝ≥0∞) (volumeMeasureOn V)).toReal ^ 2 =
        ∫ x in V, ‖F x‖ ^ (2 : ℕ) ∂MeasureTheory.volume := by
    have hraw :
        (ENNReal.toReal
            (MeasureTheory.eLpNorm F (ENNReal.ofReal (2 : ℝ)) (volumeMeasureOn V))) ^
            (2 : ℝ) =
          ∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volumeMeasureOn V) := by
      simpa using
        toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
          (μ := volumeMeasureOn V) (f := F) (p := (2 : ℝ))
          (by norm_num : (0 : ℝ) < 2)
          (by simpa using hF)
    have hraw_nat :
        (MeasureTheory.eLpNorm F (2 : ℝ≥0∞) (volumeMeasureOn V)).toReal ^ 2 =
          ∫ x, ‖F x‖ ^ (2 : ℕ) ∂(volumeMeasureOn V) := by
      simpa [Real.rpow_two] using hraw
    simpa [volumeMeasureOn, MeasureTheory.IntegrableOn] using hraw_nat
  rw [hdev]
  unfold volumeAverage
  calc
    ((MeasureTheory.volume V).toReal)⁻¹ *
        ∫ x in V, vecNormSq (F x) ∂MeasureTheory.volume
        ≤ ((MeasureTheory.volume V).toReal)⁻¹ *
            ∫ x in V, card * ‖F x‖ ^ (2 : ℕ) ∂MeasureTheory.volume :=
          mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hvol.le)
    _ = card * ((MeasureTheory.volume V).toReal)⁻¹ *
          ∫ x in V, ‖F x‖ ^ (2 : ℕ) ∂MeasureTheory.volume := by
          rw [hconst_mul]
          ring
    _ = card * ((MeasureTheory.volume V).toReal)⁻¹ *
          (MeasureTheory.eLpNorm F (2 : ℝ≥0∞) (volumeMeasureOn V)).toReal ^ 2 := by
          rw [hlp_sq]

end

end Ch01
end Book
end Homogenization
