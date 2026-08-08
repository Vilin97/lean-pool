/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CayleyMenger
import LeanPool.Erdos97ConvexOctagon.ResidualRepresentatives

/-! # Erdős 97 convex-octagon formalization: Residual Algebra10 -/

namespace Erdos97Octagon

/-- Residual class 10 has no injective planar realisation. -/
theorem residualRepresentative10_not_realises
    {p : Vertex → Plane} (hp : Function.Injective p) :
    ¬ Realises p residualRepresentative10 := by
  intro hRealises
  obtain ⟨radius, hpos, hdist⟩ :=
    exists_positive_radii hp residualRepresentative10 hRealises
  have r01 : radius 0 = radius 1 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative10])
  have r23 : radius 2 = radius 3 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative10])
  have r45 : radius 4 = radius 5 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative10])
  have r67 : radius 6 = radius 7 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative10])
  have radius0 : radius 0 = radius 0 := rfl
  have radius1 : radius 1 = radius 0 := (r01).symm
  have radius2 : radius 2 = radius 2 := rfl
  have radius3 : radius 3 = radius 2 := (r23).symm
  have radius4 : radius 4 = radius 4 := rfl
  have radius5 : radius 5 = radius 4 := (r45).symm
  have radius6 : radius 6 = radius 6 := rfl
  have radius7 : radius 7 = radius 6 := (r67).symm
  let base : ℝ := radius 0 ^ 2
  have hbase : base ≠ 0 := by
    dsimp [base]
    exact pow_ne_zero 2 (ne_of_gt (hpos 0))
  let s1 : ℝ := radius 2 ^ 2 / base
  let s2 : ℝ := radius 4 ^ 2 / base
  let s3 : ℝ := radius 6 ^ 2 / base
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
  have d06 : sqDist (p 0) (p 6) / base = s3 := by
    rw [sqDist, dist_comm, hdist 6 0 (by decide), radius6]
  have d07 : sqDist (p 0) (p 7) / base = s3 := by
    rw [sqDist, dist_comm, hdist 7 0 (by decide), radius7]
  have d12 : sqDist (p 1) (p 2) / base = 1 := by
    rw [sqDist, hdist 1 2 (by decide), radius1]
    exact div_self hbase
  have d13 : sqDist (p 1) (p 3) / base = 1 := by
    rw [sqDist, hdist 1 3 (by decide), radius1]
    exact div_self hbase
  have d14 : sqDist (p 1) (p 4) / base = s2 := by
    rw [sqDist, dist_comm, hdist 4 1 (by decide), radius4]
  have d16 : sqDist (p 1) (p 6) / base = s3 := by
    rw [sqDist, dist_comm, hdist 6 1 (by decide), radius6]
  have d17 : sqDist (p 1) (p 7) / base = s3 := by
    rw [sqDist, dist_comm, hdist 7 1 (by decide), radius7]
  have d23 : sqDist (p 2) (p 3) / base = s1 := by
    rw [sqDist, hdist 2 3 (by decide), radius2]
  have d24 : sqDist (p 2) (p 4) / base = s1 := by
    rw [sqDist, hdist 2 4 (by decide), radius2]
  have d26 : sqDist (p 2) (p 6) / base = s1 := by
    rw [sqDist, hdist 2 6 (by decide), radius2]
  have d27 : sqDist (p 2) (p 7) / base = s3 := by
    rw [sqDist, dist_comm, hdist 7 2 (by decide), radius7]
  have d45 : sqDist (p 4) (p 5) / base = s2 := by
    rw [sqDist, hdist 4 5 (by decide), radius4]
  have d46 : sqDist (p 4) (p 6) / base = s2 := by
    rw [sqDist, hdist 4 6 (by decide), radius4]
  have d47 : sqDist (p 4) (p 7) / base = s2 := by
    rw [sqDist, hdist 4 7 (by decide), radius4]
  have d56 : sqDist (p 5) (p 6) / base = s2 := by
    rw [sqDist, hdist 5 6 (by decide), radius5]
  have d57 : sqDist (p 5) (p 7) / base = s2 := by
    rw [sqDist, hdist 5 7 (by decide), radius5]
  have d67 : sqDist (p 6) (p 7) / base = s3 := by
    rw [sqDist, hdist 6 7 (by decide), radius6]
  have hcm0 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 4) hbase
  rw [d01, d02, d04, d12, d14, d24] at hcm0
  have e0 : -2*s1  ^  2 + 2*s1*s2 + 4*s1 - 2*s2  ^  2 + 4*s2 - 2 = 0 := by
    dsimp [cm4] at hcm0
    nlinarith only [hcm0]
  have hcm1 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 6) hbase
  rw [d01, d02, d06, d12, d16, d26] at hcm1
  have e1 : -2*s1  ^  2 + 4*s1*s3 + 2*s1 - 2*s3  ^  2 + 4*s3 - 2 = 0 := by
    dsimp [cm4] at hcm1
    nlinarith only [hcm1]
  have hcm2 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 3) hbase
  rw [d01, d02, d03, d12, d13, d23] at hcm2
  have e2 : -2*s1  ^  2 + 6*s1 = 0 := by
    dsimp [cm4] at hcm2
    nlinarith only [hcm2]
  have hcm3 := cm4_normalized_eq_zero
    (p 4) (p 5) (p 6) (p 7) hbase
  rw [d45, d46, d47, d56, d57, d67] at hcm3
  have e3 : 6*s2  ^  2*s3 - 2*s2*s3  ^  2 = 0 := by
    dsimp [cm4] at hcm3
    nlinarith only [hcm3]
  have hcm4 := cm4_normalized_eq_zero
    (p 0) (p 5) (p 6) (p 7) hbase
  rw [d05, d06, d07, d56, d57, d67] at hcm4
  have e4 : 6*s2*s3  ^  2 - 2*s3  ^  3 = 0 := by
    dsimp [cm4] at hcm4
    nlinarith only [hcm4]
  have hcm5 := cm4_normalized_eq_zero
    (p 0) (p 1) (p 2) (p 7) hbase
  rw [d01, d02, d07, d12, d17, d27] at hcm5
  have e5 : 6*s3 - 2 = 0 := by
    dsimp [cm4] at hcm5
    nlinarith only [hcm5]
  have certificate :
      (-81/80 : ℝ) * (-2*s1  ^  2 + 2*s1*s2 + 4*s1 - 2*s2  ^  2 + 4*s2 - 2) +
        (-243/320*s2+243/320 : ℝ) * (-2*s1  ^  2 + 4*s1*s3 + 2*s1 - 2*s3  ^  2 + 4*s3 - 2) +
        (243/320*s2+81/320 : ℝ) * (-2*s1  ^  2 + 6*s1) +
        (-81/80 : ℝ) * (6*s2  ^  2*s3 - 2*s2*s3  ^  2) +
        (189/40 : ℝ) * (6*s2*s3  ^  2 - 2*s3  ^  3) +
        (81/160*s1*s2-81/160*s1+81/80*s2 ^ 2-1701/320*s2*s3-81/64*s2+
            63/40*s3 ^ 2+249/320*s3-79/320 : ℝ) *
          (6*s3 - 2) = 1 := by
    ring
  rw [e0, e1, e2, e3, e4, e5] at certificate
  norm_num at certificate

end Erdos97Octagon
