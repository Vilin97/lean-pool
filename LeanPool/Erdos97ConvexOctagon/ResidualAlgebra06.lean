/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CayleyMenger
import LeanPool.Erdos97ConvexOctagon.ResidualRepresentatives

/-! # Erdős 97 convex-octagon formalization: Residual Algebra06 -/

namespace Erdos97Octagon

/-- Residual class 6 has no injective planar realisation. -/
theorem residualRepresentative06_not_realises
    {p : Vertex → Plane} (hp : Function.Injective p) :
    ¬ Realises p residualRepresentative06 := by
  intro hRealises
  obtain ⟨radius, hpos, hdist⟩ :=
    exists_positive_radii hp residualRepresentative06 hRealises
  have r01 : radius 0 = radius 1 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative06])
  have r02 : radius 0 = radius 2 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative06])
  have r03 : radius 0 = radius 3 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative06])
  have r46 : radius 4 = radius 6 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative06])
  have r47 : radius 4 = radius 7 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative06])
  have r65 : radius 6 = radius 5 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative06])
  have radius0 : radius 0 = radius 0 := rfl
  have radius1 : radius 1 = radius 0 := (r01).symm
  have radius2 : radius 2 = radius 0 := (r02).symm
  have radius3 : radius 3 = radius 0 := (r03).symm
  have radius4 : radius 4 = radius 4 := rfl
  have radius5 : radius 5 = radius 4 := ((r46).trans r65).symm
  have radius6 : radius 6 = radius 4 := (r46).symm
  have radius7 : radius 7 = radius 4 := (r47).symm
  let base : ℝ := radius 0 ^ 2
  have hbase : base ≠ 0 := by
    dsimp [base]
    exact pow_ne_zero 2 (ne_of_gt (hpos 0))
  let s1 : ℝ := radius 4 ^ 2 / base
  have d01 : sqDist (p 0) (p 1) / base = 1 := by
    rw [sqDist, hdist 0 1 (by decide), radius0]
    exact div_self hbase
  have d02 : sqDist (p 0) (p 2) / base = 1 := by
    rw [sqDist, hdist 0 2 (by decide), radius0]
    exact div_self hbase
  have d04 : sqDist (p 0) (p 4) / base = 1 := by
    rw [sqDist, hdist 0 4 (by decide), radius0]
    exact div_self hbase
  have d05 : sqDist (p 0) (p 5) / base = s1 := by
    rw [sqDist, dist_comm, hdist 5 0 (by decide), radius5]
  have d12 : sqDist (p 1) (p 2) / base = 1 := by
    rw [sqDist, hdist 1 2 (by decide), radius1]
    exact div_self hbase
  have d14 : sqDist (p 1) (p 4) / base = s1 := by
    rw [sqDist, dist_comm, hdist 4 1 (by decide), radius4]
  have d15 : sqDist (p 1) (p 5) / base = 1 := by
    rw [sqDist, hdist 1 5 (by decide), radius1]
    exact div_self hbase
  have d24 : sqDist (p 2) (p 4) / base = 1 := by
    rw [sqDist, hdist 2 4 (by decide), radius2]
    exact div_self hbase
  have d25 : sqDist (p 2) (p 5) / base = s1 := by
    rw [sqDist, dist_comm, hdist 5 2 (by decide), radius5]
  have d26 : sqDist (p 2) (p 6) / base = 1 := by
    rw [sqDist, hdist 2 6 (by decide), radius2]
    exact div_self hbase
  have d27 : sqDist (p 2) (p 7) / base = s1 := by
    rw [sqDist, dist_comm, hdist 7 2 (by decide), radius7]
  have d56 : sqDist (p 5) (p 6) / base = s1 := by
    rw [sqDist, hdist 5 6 (by decide), radius5]
  have d57 : sqDist (p 5) (p 7) / base = s1 := by
    rw [sqDist, hdist 5 7 (by decide), radius5]
  have d67 : sqDist (p 6) (p 7) / base = s1 := by
    rw [sqDist, hdist 6 7 (by decide), radius6]
  have hcm0 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 4) hbase
  rw [d01, d02, d04, d12, d14, d24] at hcm0
  have e0 : -2*s1  ^  2 + 6*s1 = 0 := by
    dsimp [cm4] at hcm0
    nlinarith only [hcm0]
  have hcm1 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 5) hbase
  rw [d01, d02, d05, d12, d15, d25] at hcm1
  have e1 : -2*s1  ^  2 + 8*s1 - 2 = 0 := by
    dsimp [cm4] at hcm1
    nlinarith only [hcm1]
  have hcm2 := cm4_normalized_eq_zero
    (p 2) (p 5) (p 6) (p 7) hbase
  rw [d25, d26, d27, d56, d57, d67] at hcm2
  have e2 : 6*s1  ^  2 - 2*s1 = 0 := by
    dsimp [cm4] at hcm2
    nlinarith only [hcm2]
  have certificate :
      (11/16 : ℝ) * (-2*s1  ^  2 + 6*s1) +
        (-1/2 : ℝ) * (-2*s1  ^  2 + 8*s1 - 2) +
        (1/16 : ℝ) * (6*s1  ^  2 - 2*s1) = 1 := by
    ring
  rw [e0, e1, e2] at certificate
  norm_num at certificate

end Erdos97Octagon
