/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CayleyMenger
import LeanPool.Erdos97ConvexOctagon.ResidualRepresentatives

/-! # Erdős 97 convex-octagon formalization: Residual Algebra12 -/

namespace Erdos97Octagon

/-- Residual class 12 has no injective planar realisation. -/
theorem residualRepresentative12_not_realises
    {p : Vertex → Plane} (hp : Function.Injective p) :
    ¬ Realises p residualRepresentative12 := by
  intro hRealises
  obtain ⟨radius, hpos, hdist⟩ :=
    exists_positive_radii hp residualRepresentative12 hRealises
  have r01 : radius 0 = radius 1 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative12])
  have r25 : radius 2 = radius 5 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative12])
  have r37 : radius 3 = radius 7 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative12])
  have r46 : radius 4 = radius 6 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative12])
  have radius0 : radius 0 = radius 0 := rfl
  have radius1 : radius 1 = radius 0 := (r01).symm
  have radius2 : radius 2 = radius 2 := rfl
  have radius5 : radius 5 = radius 2 := (r25).symm
  have radius3 : radius 3 = radius 3 := rfl
  have radius7 : radius 7 = radius 3 := (r37).symm
  have radius4 : radius 4 = radius 4 := rfl
  have radius6 : radius 6 = radius 4 := (r46).symm
  let base : ℝ := radius 0 ^ 2
  have hbase : base ≠ 0 := by
    dsimp [base]
    exact pow_ne_zero 2 (ne_of_gt (hpos 0))
  let s1 : ℝ := radius 2 ^ 2 / base
  let s2 : ℝ := radius 3 ^ 2 / base
  let s3 : ℝ := radius 4 ^ 2 / base
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
  have d06 : sqDist (p 0) (p 6) / base = s3 := by
    rw [sqDist, dist_comm, hdist 6 0 (by decide), radius6]
  have d07 : sqDist (p 0) (p 7) / base = s2 := by
    rw [sqDist, dist_comm, hdist 7 0 (by decide), radius7]
  have d13 : sqDist (p 1) (p 3) / base = s2 := by
    rw [sqDist, dist_comm, hdist 3 1 (by decide), radius3]
  have d14 : sqDist (p 1) (p 4) / base = s3 := by
    rw [sqDist, dist_comm, hdist 4 1 (by decide), radius4]
  have d16 : sqDist (p 1) (p 6) / base = 1 := by
    rw [sqDist, hdist 1 6 (by decide), radius1]
    exact div_self hbase
  have d24 : sqDist (p 2) (p 4) / base = s3 := by
    rw [sqDist, dist_comm, hdist 4 2 (by decide), radius4]
  have d27 : sqDist (p 2) (p 7) / base = s2 := by
    rw [sqDist, dist_comm, hdist 7 2 (by decide), radius7]
  have d34 : sqDist (p 3) (p 4) / base = s2 := by
    rw [sqDist, hdist 3 4 (by decide), radius3]
  have d36 : sqDist (p 3) (p 6) / base = s3 := by
    rw [sqDist, dist_comm, hdist 6 3 (by decide), radius6]
  have d37 : sqDist (p 3) (p 7) / base = s2 := by
    rw [sqDist, hdist 3 7 (by decide), radius3]
  have d46 : sqDist (p 4) (p 6) / base = s3 := by
    rw [sqDist, hdist 4 6 (by decide), radius4]
  have d47 : sqDist (p 4) (p 7) / base = s3 := by
    rw [sqDist, hdist 4 7 (by decide), radius4]
  have d67 : sqDist (p 6) (p 7) / base = s2 := by
    rw [sqDist, dist_comm, hdist 7 6 (by decide), radius7]
  have hcm0 := cm4_normalized_eq_zero
    (p 0) (p 2) (p 4) (p 7) hbase
  rw [d02, d04, d07, d24, d27, d47] at hcm0
  have e0 : -2*s2  ^  2 - 2*s2*s3  ^  2 + 10*s2*s3 - 2*s3 = 0 := by
    dsimp [cm4] at hcm0
    nlinarith only [hcm0]
  have hcm1 := cm4_normalized_eq_zero
    (p 0) (p 4) (p 6) (p 7) hbase
  rw [d04, d06, d07, d46, d47, d67] at hcm1
  have e1 : -2*s2  ^  2*s3 + 4*s2*s3  ^  2 + 6*s2*s3 - 2*s2 - 2*s3  ^  3 = 0 := by
    dsimp [cm4] at hcm1
    nlinarith only [hcm1]
  have hcm2 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 3) (p 6) hbase
  rw [d01, d03, d06, d13, d16, d36] at hcm2
  have e2 : -2*s2  ^  2*s3 + 6*s2*s3 - 2*s3  ^  2 + 4*s3 - 2 = 0 := by
    dsimp [cm4] at hcm2
    nlinarith only [hcm2]
  have hcm3 := cm4_normalized_eq_zero
    (p 0) (p 3) (p 4) (p 6) hbase
  rw [d03, d04, d06, d34, d36, d46] at hcm3
  have e3 : -2*s2  ^  2*s3 + 8*s2*s3 - 2*s2 = 0 := by
    dsimp [cm4] at hcm3
    nlinarith only [hcm3]
  have hcm4 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 3) (p 4) hbase
  rw [d01, d03, d04, d13, d14, d34] at hcm4
  have e4 : -2*s2  ^  2*s3 + 8*s2*s3 - 2*s3  ^  2 = 0 := by
    dsimp [cm4] at hcm4
    nlinarith only [hcm4]
  have hcm5 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 4) (p 6) hbase
  rw [d01, d04, d06, d14, d16, d46] at hcm5
  have e5 : -2*s3  ^  3 + 4*s3  ^  2 + 4*s3 - 2 = 0 := by
    dsimp [cm4] at hcm5
    nlinarith only [hcm5]
  have hcm6 := cm4_normalized_eq_zero
    (p 0) (p 3) (p 6) (p 7) hbase
  rw [d03, d06, d07, d36, d37, d67] at hcm6
  have e6 : 8*s2*s3 - 2*s2 - 2*s3  ^  2 = 0 := by
    dsimp [cm4] at hcm6
    nlinarith only [hcm6]
  have certificate :
      (-1 : ℝ) * (-2*s2  ^  2 - 2*s2*s3  ^  2 + 10*s2*s3 - 2*s3) +
        (7/6 : ℝ) * (-2*s2  ^  2*s3 + 4*s2*s3  ^  2 + 6*s2*s3 - 2*s2 - 2*s3  ^  3) +
        (1/12 : ℝ) * (-2*s2  ^  2*s3 + 6*s2*s3 - 2*s3  ^  2 + 4*s3 - 2) +
        (17/12 : ℝ) * (-2*s2  ^  2*s3 + 8*s2*s3 - 2*s2) +
        (4/3 : ℝ) * (-2*s2  ^  2*s3 + 8*s2*s3 - 2*s3  ^  2) +
        (-7/12 : ℝ) * (-2*s3  ^  3 + 4*s3  ^  2 + 4*s3 - 2) +
        (s2-7/12*s3-31/12 : ℝ) * (8*s2*s3 - 2*s2 - 2*s3  ^  2) = 1 := by
    ring
  rw [e0, e1, e2, e3, e4, e5, e6] at certificate
  norm_num at certificate

end Erdos97Octagon
