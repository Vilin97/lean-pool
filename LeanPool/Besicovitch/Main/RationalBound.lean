/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Main.Bound
public import LeanPool.Besicovitch.SixPoint.GramWeightedBound

/-!
# The rational planar bound

The Gram certificates give the weighted geometric bound at the small rational weights, the finite
failure tree turns that into the six-point finite property at `barS = 6934/10000`, and the
six-point transfer turns that into the planar rectifiability bound.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- Every threshold above `barS` forces one-rectifiability in the plane. -/
theorem forcesOneRectifiability_plane_of_barS_lt {β : ℝ} (hβ : barS < β) :
    ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β) :=
  (sixPointFiniteProperty_barS_of_weightedGeometricBound gramLambda_pos gramMu_pos
    weightedGeometricBound_gram).forcesOneRectifiability_of_gt barS_pos barS_lt_one hβ

/-- The planar one-dimensional rectifiability threshold is at most `6934/10000`. -/
theorem sigmaOne_plane_le_barS :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 := by
  have hfinite : SixPointFiniteProperty barS :=
    sixPointFiniteProperty_barS_of_weightedGeometricBound gramLambda_pos gramMu_pos
      weightedGeometricBound_gram
  have hbound := hfinite.sigmaOne_plane_le barS_pos barS_lt_one
  rwa [barS_eq] at hbound

end LeanPool.Besicovitch
