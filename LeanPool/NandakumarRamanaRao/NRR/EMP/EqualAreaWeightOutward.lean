/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.AreaVectorTarget
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CompactSiteFamily
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.BodyCellPartition
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAreaVector
/-!
# Outward estimates for the equal-area deviation map

This module supplies the coercive estimate needed by the finite-dimensional existence argument.
For a normalized weight vector, let `M` be its largest coordinate.  Every restricted power cell
with positive area belongs to an index whose weight is at least `M - C`, where `C` is an explicit
body/site bound.  Consequently the scalar pairing of the weight vector with its area-deviation
vector is at least `(M - C) * K.area`.
-/

open NRR NRR.Geometry MeasureTheory

namespace NRR
namespace EMP

variable {n : Nat}

/-- A finite upper bound for the norms of all sites. -/
noncomputable def finiteSiteRadius (s : Fin n → Plane) : Real :=
  ∑ i, ‖s i‖

lemma finiteSiteRadius_nonneg (s : Fin n → Plane) :
    0 ≤ finiteSiteRadius s := by
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_site_le_finiteSiteRadius (s : Fin n → Plane) (i : Fin n) :
    ‖s i‖ ≤ finiteSiteRadius s := by
  unfold finiteSiteRadius
  exact Finset.single_le_sum (fun j _ => norm_nonneg (s j)) (Finset.mem_univ i)

/-- Uniform power-distance gap bound on the compact body. -/
noncomputable def powerGapBound
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) : Real :=
  (VariableBody.parentRadius K + finiteSiteRadius s) ^ 2

lemma powerGapBound_nonneg
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) :
    0 ≤ powerGapBound K s := by
  unfold powerGapBound
  positivity

/-- If the `i`-th restricted cell is nonempty, no other weight exceeds `w i` by more than the
uniform geometric gap bound. -/
lemma weight_sub_le_powerGapBound_of_bodyCellSet_nonempty
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → Real)
    {i : Fin n}
    (hi : (PowerDiagram.bodyCellSet K s w i).Nonempty)
    (j : Fin n) :
    w j - w i ≤ powerGapBound K s := by
  obtain ⟨x, hxK, hxi⟩ := hi
  have hle : PowerDiagram.powerDist s w i x ≤ PowerDiagram.powerDist s w j x :=
    (PowerDiagram.mem_cell s w i x).mp hxi j
  have hnorm : ‖x - s j‖ ≤
      VariableBody.parentRadius K + finiteSiteRadius s :=
    calc
      ‖x - s j‖ ≤ ‖x‖ + ‖s j‖ := norm_sub_le _ _
      _ ≤ VariableBody.parentRadius K + finiteSiteRadius s :=
        add_le_add
          (VariableBody.norm_mem_parent_le_parentRadius K hxK)
          (norm_site_le_finiteSiteRadius s j)
  have hsq : ‖x - s j‖ ^ 2 ≤ powerGapBound K s := by
    unfold powerGapBound
    nlinarith [hnorm, norm_nonneg (x - s j),
      VariableBody.parentRadius_nonneg K, finiteSiteRadius_nonneg s]
  simp only [PowerDiagram.powerDist] at hle
  nlinarith [hsq, sq_nonneg ‖x - s i‖]

/-- A nonzero restricted-cell area implies that the restricted cell is nonempty. -/
lemma bodyCellSet_nonempty_of_areaVec_ne_zero
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → Real)
    (i : Fin n) (hi : EMP.areaVec K s w i ≠ 0) :
    (PowerDiagram.bodyCellSet K s w i).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  apply hi
  change PowerDiagram.bodyCellArea K s w i = 0
  unfold PowerDiagram.bodyCellArea
  have hmeasure : volume (PowerDiagram.bodyCellSet K s w i) = 0 := by
    rw [hempty]
    simp
  rw [hmeasure]
  simp

/-- Restricted power-cell areas are nonnegative. -/
lemma areaVec_nonneg
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → Real)
    (i : Fin n) :
    0 ≤ EMP.areaVec K s w i := by
  simp [EMP.areaVec, PowerDiagram.areaVec, PowerDiagram.bodyCellArea]

/-- Pairing of weights with the area-deviation vector. -/
noncomputable def deviationPairing
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → Real) : Real :=
  ∑ i, w i * EMP.areaDeviation K s w i

/-- For normalized weights, the target part of the pairing vanishes. -/
lemma deviationPairing_eq_weightedArea_of_normalized
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → Real)
    (hw : EMP.WeightNormalized w) :
    deviationPairing K s w = ∑ i, w i * EMP.areaVec K s w i := by
  unfold deviationPairing EMP.areaDeviation EMP.equalAreaTarget
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have htarget : ∑ i : Fin n, w i * (K.area / (n : Real)) = 0 := by
    rw [← Finset.sum_mul]
    simp only [EMP.WeightNormalized, EMP.weightSum] at hw
    rw [hw, zero_mul]
  rw [htarget, sub_zero]

/-- Coercive lower bound for the deviation pairing in terms of a maximal weight coordinate. -/
lemma deviationPairing_lower_bound_of_max
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : Fin n → Real) (hw : EMP.WeightNormalized w)
    (k : Fin n) (hk : ∀ i, w i ≤ w k) :
    (w k - powerGapBound K s) * K.area ≤ deviationPairing K s w := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hterm : ∀ i : Fin n,
      (w k - powerGapBound K s) * EMP.areaVec K s w i ≤
        w i * EMP.areaVec K s w i := by
    intro i
    have hai := areaVec_nonneg K s w i
    by_cases hzero : EMP.areaVec K s w i = 0
    · simp only [hzero, mul_zero, le_refl]
    · have hne := bodyCellSet_nonempty_of_areaVec_ne_zero K s w i hzero
      have hgap := weight_sub_le_powerGapBound_of_bodyCellSet_nonempty K s w hne k
      exact mul_le_mul_of_nonneg_right (by linarith) hai
  rw [deviationPairing_eq_weightedArea_of_normalized K s w hw]
  calc
    (w k - powerGapBound K s) * K.area =
        (w k - powerGapBound K s) * (∑ i, EMP.areaVec K s w i) := by
          rw [NRR.sum_EMP_areaVec_eq_area K s w hs]
    _ = ∑ i, (w k - powerGapBound K s) * EMP.areaVec K s w i := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i, w i * EMP.areaVec K s w i :=
          Finset.sum_le_sum fun i _ => hterm i

/-- In particular, once a maximal normalized weight exceeds the geometric gap bound, the
weight/deviation pairing is strictly positive. -/
lemma deviationPairing_pos_of_max_gt
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : Fin n → Real) (hw : EMP.WeightNormalized w)
    (k : Fin n) (hk : ∀ i, w i ≤ w k)
    (hlarge : powerGapBound K s < w k) :
    0 < deviationPairing K s w := by
  have hK : 0 < K.area :=
    (NRR.SolidConvexBody.ofConvexBody K).area_pos
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hlarge) hK)
    (deviationPairing_lower_bound_of_max K s hn hs w hw k hk)

end EMP
end NRR
