/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CayleyMenger
import LeanPool.Erdos97ConvexOctagon.ResidualRepresentatives

/-! # Erdős 97 convex-octagon formalization: Residual Algebra04 -/

namespace Erdos97Octagon

/-- Residual class 4 has no injective planar realisation. -/
theorem residualRepresentative04_not_realises
    {p : Vertex → Plane} (hp : Function.Injective p) :
    ¬ Realises p residualRepresentative04 := by
  intro hRealises
  obtain ⟨radius, hpos, hdist⟩ :=
    exists_positive_radii hp residualRepresentative04 hRealises
  have r01 : radius 0 = radius 1 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative04])
  have r02 : radius 0 = radius 2 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative04])
  have r34 : radius 3 = radius 4 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative04])
  have r56 : radius 5 = radius 6 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative04])
  have r57 : radius 5 = radius 7 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative04])
  have radius0 : radius 0 = radius 0 := rfl
  have radius1 : radius 1 = radius 0 := (r01).symm
  have radius2 : radius 2 = radius 0 := (r02).symm
  have radius3 : radius 3 = radius 3 := rfl
  have radius4 : radius 4 = radius 3 := (r34).symm
  have radius5 : radius 5 = radius 5 := rfl
  have radius6 : radius 6 = radius 5 := (r56).symm
  have radius7 : radius 7 = radius 5 := (r57).symm
  let base : ℝ := radius 0 ^ 2
  have hbase : base ≠ 0 := by
    dsimp [base]
    exact pow_ne_zero 2 (ne_of_gt (hpos 0))
  let s1 : ℝ := radius 3 ^ 2 / base
  let s2 : ℝ := radius 5 ^ 2 / base
  have d01 : sqDist (p 0) (p 1) / base = 1 := by
    rw [sqDist, hdist 0 1 (by decide), radius0]
    exact div_self hbase
  have d02 : sqDist (p 0) (p 2) / base = 1 := by
    rw [sqDist, hdist 0 2 (by decide), radius0]
    exact div_self hbase
  have d03 : sqDist (p 0) (p 3) / base = 1 := by
    rw [sqDist, hdist 0 3 (by decide), radius0]
    exact div_self hbase
  have d04 : sqDist (p 0) (p 4) / base = 1 := by
    rw [sqDist, hdist 0 4 (by decide), radius0]
    exact div_self hbase
  have d05 : sqDist (p 0) (p 5) / base = s2 := by
    rw [sqDist, dist_comm, hdist 5 0 (by decide), radius5]
  have d12 : sqDist (p 1) (p 2) / base = 1 := by
    rw [sqDist, hdist 1 2 (by decide), radius1]
    exact div_self hbase
  have d13 : sqDist (p 1) (p 3) / base = 1 := by
    rw [sqDist, hdist 1 3 (by decide), radius1]
    exact div_self hbase
  have d14 : sqDist (p 1) (p 4) / base = s1 := by
    rw [sqDist, dist_comm, hdist 4 1 (by decide), radius4]
  have d15 : sqDist (p 1) (p 5) / base = 1 := by
    rw [sqDist, hdist 1 5 (by decide), radius1]
    exact div_self hbase
  have d17 : sqDist (p 1) (p 7) / base = s2 := by
    rw [sqDist, dist_comm, hdist 7 1 (by decide), radius7]
  have d23 : sqDist (p 2) (p 3) / base = s1 := by
    rw [sqDist, dist_comm, hdist 3 2 (by decide), radius3]
  have d24 : sqDist (p 2) (p 4) / base = 1 := by
    rw [sqDist, hdist 2 4 (by decide), radius2]
    exact div_self hbase
  let w2_5 : ℝ := sqDist (p 2) (p 5) / base
  have d25 : sqDist (p 2) (p 5) / base = w2_5 := rfl
  have d34 : sqDist (p 3) (p 4) / base = s1 := by
    rw [sqDist, hdist 3 4 (by decide), radius3]
  have d35 : sqDist (p 3) (p 5) / base = s2 := by
    rw [sqDist, dist_comm, hdist 5 3 (by decide), radius5]
  have d45 : sqDist (p 4) (p 5) / base = s1 := by
    rw [sqDist, hdist 4 5 (by decide), radius4]
  have d47 : sqDist (p 4) (p 7) / base = s1 := by
    rw [sqDist, hdist 4 7 (by decide), radius4]
  have d57 : sqDist (p 5) (p 7) / base = s2 := by
    rw [sqDist, hdist 5 7 (by decide), radius5]
  have hcm0 := cm4_normalized_eq_zero
    (p 0) (p 2) (p 4) (p 5) hbase
  rw [d02, d04, d05, d24, d25, d45] at hcm0
  have e0 :
      -2*s1  ^  2 + 2*s1*s2 + 2*s1*w2_5 + 2*s1 - 2*s2  ^  2 +
          2*s2*w2_5 + 2*s2 - 2*w2_5  ^  2 + 2*w2_5 - 2 = 0 := by
    dsimp [cm4] at hcm0
    nlinarith only [hcm0]
  have hcm1 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 3) hbase
  rw [d01, d02, d03, d12, d13, d23] at hcm1
  have e1 : -2*s1  ^  2 + 6*s1 = 0 := by
    dsimp [cm4] at hcm1
    nlinarith only [hcm1]
  have hcm2 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 3) (p 4) hbase
  rw [d01, d03, d04, d13, d14, d34] at hcm2
  have e2 : -2*s1  ^  2 + 8*s1 - 2 = 0 := by
    dsimp [cm4] at hcm2
    nlinarith only [hcm2]
  have hcm3 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 5) hbase
  rw [d01, d02, d05, d12, d15, d25] at hcm3
  have e3 : -2*s2  ^  2 + 2*s2*w2_5 + 4*s2 - 2*w2_5  ^  2 + 4*w2_5 - 2 = 0 := by
    dsimp [cm4] at hcm3
    nlinarith only [hcm3]
  have hcm4 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 3) (p 5) hbase
  rw [d01, d03, d05, d13, d15, d35] at hcm4
  have e4 : -2*s2  ^  2 + 8*s2 - 2 = 0 := by
    dsimp [cm4] at hcm4
    nlinarith only [hcm4]
  have hcm5 := cm4_normalized_eq_zero
    (p 1) (p 4) (p 5) (p 7) hbase
  rw [d14, d15, d17, d45, d47, d57] at hcm5
  have e5 : 8*s1*s2 - 2*s1 - 2*s2  ^  2 = 0 := by
    dsimp [cm4] at hcm5
    nlinarith only [hcm5]
  have certificate :
      (-1/4 : ℝ) *
          (-2*s1  ^  2 + 2*s1*s2 + 2*s1*w2_5 + 2*s1 - 2*s2  ^  2 +
            2*s2*w2_5 + 2*s2 - 2*w2_5  ^  2 + 2*w2_5 - 2) +
        (-1/4*w2_5+11/16 : ℝ) * (-2*s1  ^  2 + 6*s1) +
        (1/4*w2_5-7/16 : ℝ) * (-2*s1  ^  2 + 8*s1 - 2) +
        (1/4 : ℝ) * (-2*s2  ^  2 + 2*s2*w2_5 + 4*s2 - 2*w2_5  ^  2 + 4*w2_5 - 2) +
        (-1/16 : ℝ) * (-2*s2  ^  2 + 8*s2 - 2) +
        (1/16 : ℝ) * (8*s1*s2 - 2*s1 - 2*s2  ^  2) = 1 := by
    ring
  rw [e0, e1, e2, e3, e4, e5] at certificate
  norm_num at certificate

end Erdos97Octagon
