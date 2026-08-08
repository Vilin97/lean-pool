/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CayleyMenger
import LeanPool.Erdos97ConvexOctagon.ResidualRepresentatives

/-! # Erdős 97 convex-octagon formalization: Residual Algebra03 -/

namespace Erdos97Octagon

/-- Residual class 3 has no injective planar realisation. -/
theorem residualRepresentative03_not_realises
    {p : Vertex → Plane} (hp : Function.Injective p) :
    ¬ Realises p residualRepresentative03 := by
  intro hRealises
  obtain ⟨radius, hpos, hdist⟩ :=
    exists_positive_radii hp residualRepresentative03 hRealises
  have r01 : radius 0 = radius 1 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative03])
  have r02 : radius 0 = radius 2 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative03])
  have r03 : radius 0 = radius 3 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative03])
  have r04 : radius 0 = radius 4 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative03])
  have r56 : radius 5 = radius 6 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative03])
  have r57 : radius 5 = radius 7 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative03])
  have radius0 : radius 0 = radius 0 := rfl
  have radius1 : radius 1 = radius 0 := (r01).symm
  have radius2 : radius 2 = radius 0 := (r02).symm
  have radius3 : radius 3 = radius 0 := (r03).symm
  have radius4 : radius 4 = radius 0 := (r04).symm
  have radius5 : radius 5 = radius 5 := rfl
  have radius6 : radius 6 = radius 5 := (r56).symm
  have radius7 : radius 7 = radius 5 := (r57).symm
  let base : ℝ := radius 0 ^ 2
  have hbase : base ≠ 0 := by
    dsimp [base]
    exact pow_ne_zero 2 (ne_of_gt (hpos 0))
  let s1 : ℝ := radius 5 ^ 2 / base
  have d13 : sqDist (p 1) (p 3) / base = 1 := by
    rw [sqDist, hdist 1 3 (by decide), radius1]
    exact div_self hbase
  have d15 : sqDist (p 1) (p 5) / base = 1 := by
    rw [sqDist, hdist 1 5 (by decide), radius1]
    exact div_self hbase
  have d16 : sqDist (p 1) (p 6) / base = s1 := by
    rw [sqDist, dist_comm, hdist 6 1 (by decide), radius6]
  have d17 : sqDist (p 1) (p 7) / base = s1 := by
    rw [sqDist, dist_comm, hdist 7 1 (by decide), radius7]
  have d35 : sqDist (p 3) (p 5) / base = 1 := by
    rw [sqDist, hdist 3 5 (by decide), radius3]
    exact div_self hbase
  have d36 : sqDist (p 3) (p 6) / base = s1 := by
    rw [sqDist, dist_comm, hdist 6 3 (by decide), radius6]
  have d37 : sqDist (p 3) (p 7) / base = 1 := by
    rw [sqDist, hdist 3 7 (by decide), radius3]
    exact div_self hbase
  have d56 : sqDist (p 5) (p 6) / base = s1 := by
    rw [sqDist, hdist 5 6 (by decide), radius5]
  have d57 : sqDist (p 5) (p 7) / base = s1 := by
    rw [sqDist, hdist 5 7 (by decide), radius5]
  have hcm0 := cm4_normalized_eq_zero
    (p 1) (p 3) (p 5) (p 7) hbase
  rw [d13, d15, d17, d35, d37, d57] at hcm0
  have e0 : -2*s1  ^  2 + 8*s1 - 2 = 0 := by
    dsimp [cm4] at hcm0
    nlinarith only [hcm0]
  have hcm1 := cm4_normalized_eq_zero
    (p 1) (p 3) (p 5) (p 6) hbase
  rw [d13, d15, d16, d35, d36, d56] at hcm1
  have e1 : 6*s1 - 2 = 0 := by
    dsimp [cm4] at hcm1
    nlinarith only [hcm1]
  have certificate :
      (9/4 : ℝ) * (-2*s1  ^  2 + 8*s1 - 2) +
        (3/4*s1-11/4 : ℝ) * (6*s1 - 2) = 1 := by
    ring
  rw [e0, e1] at certificate
  norm_num at certificate

end Erdos97Octagon
